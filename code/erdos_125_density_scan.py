#!/usr/bin/env python3
"""
Erdős 125 Case 2: Empirical density scan at arbitrary N.

Whereas erdos_125_density_fast.py only checks N = 4^m, this program scans
many N values in a range to look for the empirical infimum of countAB(N)/N.

This is a contribution toward the open Hasler-Melfi bound (lower density ≤
0.69616). Empirically we want to find scales where the ratio dips below
their theoretical upper bound — that would be new evidence for the lower
density being small.

Algorithm:
  - For each target N, compute countAB(N) = |{a + b : a ∈ A ∩ [0,N), b ∈ B ∩ [0,N), a+b < N}|
  - Output N, countAB, ratio, and find the minimum ratio seen.
  - Use the same bit-packed NumPy verifier.
"""

import argparse
import json
import sys
import time

import numpy as np


def _in_base(n: int, base: int, max_digit: int = 1) -> bool:
    while n > 0:
        if n % base > max_digit:
            return False
        n //= base
    return True


def countAB_bitmap(N: int) -> tuple:
    """Compute (countAB, density) at scale N."""
    A = np.fromiter((n for n in range(N) if _in_base(n, 3)), dtype=np.int64, count=-1)
    B = np.fromiter((n for n in range(N) if _in_base(n, 4)), dtype=np.int64, count=-1)

    nbytes = (N + 7) // 8
    bitmap = np.zeros(nbytes, dtype=np.uint8)
    byte_or_mask = np.uint8(1) << np.arange(8, dtype=np.uint8)

    n_b = B.shape[0]
    for b in B:
        sums = A + b
        valid = sums < N
        if not valid.any():
            continue
        sums_valid = sums[valid]
        byte_idx = (sums_valid >> 3).astype(np.int64)
        bit_off = (sums_valid & 7).astype(np.int64)
        per_byte_mask = byte_or_mask[bit_off]
        np.bitwise_or.at(bitmap, byte_idx, per_byte_mask)

    cab = int(np.unpackbits(bitmap).sum())
    return cab, cab / N, A.shape[0], B.shape[0]


def scan_N_range(N_min: int, N_max: int, num_samples: int = 20) -> list:
    """Scan densities at log-spaced N values between N_min and N_max."""
    log_min = np.log2(N_min)
    log_max = np.log2(N_max)
    targets = [int(2 ** x) for x in np.linspace(log_min, log_max, num_samples)]
    targets = sorted(set(targets))

    results = []
    for N in targets:
        t0 = time.time()
        cab, dens, aN, bN = countAB_bitmap(N)
        elapsed = time.time() - t0
        results.append({
            "N": N,
            "countAB": int(cab),
            "density": float(dens),
            "ratio_to_half": float(2 * dens),
            "countA_N": int(aN),
            "countB_N": int(bN),
            "elapsed": float(elapsed),
        })
        print(f"  N={N:>12,}  countAB={cab:>11,}  density={dens:.4f}  "
              f"|A|={aN:,}  |B|={bN:,}  [{elapsed:.1f}s]")

    return results


def main():
    parser = argparse.ArgumentParser(description="Erdős 125 Case 2: empirical density scan")
    parser.add_argument("--N-min", type=int, default=1024)
    parser.add_argument("--N-max", type=int, default=2**22,
                        help="Max scale to scan (default 2^22 = 4M)")
    parser.add_argument("--samples", type=int, default=20,
                        help="Number of log-spaced N values to sample")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    print(f"Erdős 125 Case 2 — empirical density scan")
    print(f"  N ∈ [{args.N_min:,}, {args.N_max:,}], {args.samples} samples")
    print(f"  Hasler-Melfi upper bound on lower density: 0.69616")
    print()

    results = scan_N_range(args.N_min, args.N_max, args.samples)

    print()
    densities = [r["density"] for r in results]
    min_d = min(densities)
    max_d = max(densities)
    min_N = results[densities.index(min_d)]["N"]
    max_N = results[densities.index(max_d)]["N"]
    print(f"Min empirical density: {min_d:.4f} at N={min_N:,}")
    print(f"Max empirical density: {max_d:.4f} at N={max_N:,}")
    print(f"All ratios above 1/2: {all(r['density'] >= 0.5 for r in results)}")

    if args.output:
        import os
        os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
        with open(args.output, "w") as f:
            json.dump(results, f, indent=2)
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()