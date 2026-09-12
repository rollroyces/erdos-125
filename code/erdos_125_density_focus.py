#!/usr/bin/env python3
"""
Erdős 125 Case 2: focused density scan near N = 4^15.

Generates 100 samples in a narrow window around 4^15 = 1,073,741,824
to characterize the dip shape. The hypothesis: density is sharply
lower at N = 4^15 than at nearby N.

Output: results/density_scan_near_4_15.json
"""

import argparse
import json
import sys
import time

import numpy as np

from erdos_125_density_scan import _in_base, countAB_bitmap


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--center", type=int, default=4**15,
                        help="Center N (default 4^15)")
    parser.add_argument("--span", type=float, default=0.20,
                        help="Half-width as fraction of center (default 0.20)")
    parser.add_argument("--samples", type=int, default=100,
                        help="Number of samples (default 100)")
    parser.add_argument("--output", type=str,
                        default="results/density_scan_near_4_15.json")
    args = parser.parse_args()

    N_center = args.center
    N_lo = int(N_center * (1 - args.span))
    N_hi = int(N_center * (1 + args.span))

    # Linear spacing within the window (not log) — we want fine coverage near 4^15
    targets = [int(x) for x in np.linspace(N_lo, N_hi, args.samples)]
    targets = sorted(set(targets))

    print(f"Focused density scan near N = {N_center:,}")
    print(f"  N ∈ [{N_lo:,}, {N_hi:,}], {len(targets)} samples")
    print()

    results = []
    t_start = time.time()
    for i, N in enumerate(targets):
        t0 = time.time()
        cab, dens, aN, bN = countAB_bitmap(N)
        elapsed = time.time() - t0
        frac4 = np.log(N) / np.log(4) - int(np.log(N) / np.log(4))
        results.append({
            "N": N,
            "countAB": int(cab),
            "density": float(dens),
            "ratio_to_half": float(2 * dens),
            "countA_N": int(aN),
            "countB_N": int(bN),
            "elapsed": float(elapsed),
            "frac_log4": float(frac4),
        })
        if (i + 1) % 5 == 0 or i == 0 or i == len(targets) - 1:
            print(f"  [{i+1:3d}/{len(targets)}]  N={N:>13,}  "
                  f"d={dens:.4f}  frac_4={frac4:.3f}  [{elapsed:.1f}s]")

    total = time.time() - t_start
    print()
    print(f"Total elapsed: {total:.1f}s")

    densities = [r["density"] for r in results]
    Ns = [r["N"] for r in results]
    min_d = min(densities)
    max_d = max(densities)
    min_idx = densities.index(min_d)
    max_idx = densities.index(max_d)
    print(f"Min density: {min_d:.4f} at N={Ns[min_idx]:,}")
    print(f"Max density: {max_d:.4f} at N={Ns[max_idx]:,}")
    print(f"Range: [{min_d:.4f}, {max_d:.4f}]  (spread {max_d-min_d:.4f})")

    # Compute density at exactly N = center
    exact = [r for r in results if r["N"] == N_center]
    if exact:
        print(f"Density at exactly N = {N_center:,}: {exact[0]['density']:.4f}")

    # Bucket by frac(log_4(N))
    print()
    print("Fine-grained density vs frac(log_4(N)) buckets:")
    buckets = [[] for _ in range(10)]
    for r in results:
        bi = min(int(r["frac_log4"] * 10), 9)
        buckets[bi].append(r["density"])
    for i in range(10):
        lo = i / 10
        hi = (i + 1) / 10
        if buckets[i]:
            mn = min(buckets[i])
            mx = max(buckets[i])
            mean = sum(buckets[i]) / len(buckets[i])
            print(f"  [{lo:.2f}, {hi:.2f})  n={len(buckets[i]):3d}  "
                  f"mean={mean:.4f}  min={mn:.4f}  max={mx:.4f}")

    import os
    os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
    with open(args.output, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {args.output}")


if __name__ == "__main__":
    main()