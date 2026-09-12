#!/usr/bin/env python3
"""
Erdős 125 Case 2: aggregate analysis of empirical density scans.

Reads the three scan JSON files and reports:
  - Density vs frac(log_4(N)) bucket
  - Density vs frac(log_3(N)) bucket
  - Density at N = 4^k vs nearby samples
  - Local minima of density

Output: prints analysis tables + writes results/density_insight.json
"""

import json
import math
import os
import sys


def load_all_scans(results_dir: str = "results"):
    rows = []
    for fn in ["density_scan.json", "density_scan_large.json", "density_scan_xl.json"]:
        path = os.path.join(results_dir, fn)
        if os.path.exists(path):
            with open(path) as f:
                for r in json.load(f):
                    r["source"] = fn
                    rows.append(r)
    rows.sort(key=lambda r: r["N"])
    return rows


def density_by_bucket(rows, log_base, num_buckets=10):
    """Group rows by fractional part of log_base(N)."""
    buckets = [[] for _ in range(num_buckets)]
    for r in rows:
        frac = math.log(r["N"], log_base) % 1
        bi = min(int(frac * num_buckets), num_buckets - 1)
        buckets[bi].append(r["density"])
    return [
        {
            "bucket_lo": i / num_buckets,
            "bucket_hi": (i + 1) / num_buckets,
            "n": len(ds),
            "mean": sum(ds) / len(ds) if ds else None,
            "min": min(ds) if ds else None,
            "max": max(ds) if ds else None,
        }
        for i, ds in enumerate(buckets)
    ]


def density_at_power_vs_nearby(rows, base, k_range):
    """For each k in k_range, compare density at N=base^k to nearby samples."""
    results = []
    for k in k_range:
        Nk = base ** k
        nearby = [r for r in rows if Nk * 0.7 <= r["N"] <= Nk * 1.4]
        exact = [r for r in nearby if r["N"] == Nk]
        if not exact:
            continue
        d_exact = exact[0]["density"]
        near_d = [r["density"] for r in nearby if r["N"] != Nk]
        results.append({
            "k": k,
            "base": base,
            "power": Nk,
            "density_at_power": d_exact,
            "nearby_count": len(near_d),
            "nearby_min": min(near_d) if near_d else None,
            "nearby_mean": sum(near_d) / len(near_d) if near_d else None,
            "ratio": d_exact / (sum(near_d) / len(near_d)) if near_d else None,
        })
    return results


def find_local_minima(rows, window=3):
    minima = []
    for i in range(window, len(rows) - window):
        is_min = True
        for j in range(1, window + 1):
            if (rows[i]["density"] >= rows[i - j]["density"]
                    or rows[i]["density"] >= rows[i + j]["density"]):
                is_min = False
                break
        if is_min:
            minima.append(rows[i])
    return minima


def main():
    rows = load_all_scans()
    print(f"Loaded {len(rows)} samples, N ∈ [{rows[0]['N']:,}, {rows[-1]['N']:,}]")
    print()

    print("=== Density vs frac(log_4(N)) — 10 buckets ===")
    b4 = density_by_bucket(rows, 4)
    for b in b4:
        print(f"  [{b['bucket_lo']:.2f}, {b['bucket_hi']:.2f})  "
              f"n={b['n']:2d}  mean={b['mean']:.4f}  min={b['min']:.4f}  max={b['max']:.4f}")
    print()

    print("=== Density vs frac(log_3(N)) — 10 buckets ===")
    b3 = density_by_bucket(rows, 3)
    for b in b3:
        print(f"  [{b['bucket_lo']:.2f}, {b['bucket_hi']:.2f})  "
              f"n={b['n']:2d}  mean={b['mean']:.4f}  min={b['min']:.4f}  max={b['max']:.4f}")
    print()

    print("=== Density at N=4^k vs nearby ===")
    for r in density_at_power_vs_nearby(rows, 4, range(5, 16)):
        if r["nearby_count"] > 0:
            print(f"  k={r['k']:>2}  N={r['power']:>14,}  "
                  f"d_at={r['density_at_power']:.4f}  "
                  f"d_nearby_mean={r['nearby_mean']:.4f}  "
                  f"ratio={r['ratio']:.4f}")
    print()

    print("=== Local minima (density) ===")
    for m in find_local_minima(rows, window=3):
        frac4 = math.log(m["N"], 4) % 1
        print(f"  N={m['N']:>14,}  density={m['density']:.4f}  "
              f"frac_4={frac4:.3f}")
    print()

    out = {
        "n_samples": len(rows),
        "N_min": rows[0]["N"],
        "N_max": rows[-1]["N"],
        "density_by_frac_log4_10": b4,
        "density_by_frac_log3_10": b3,
        "density_at_4k": density_at_power_vs_nearby(rows, 4, range(5, 16)),
        "local_minima": [
            {
                "N": m["N"],
                "density": m["density"],
                "frac_log4": math.log(m["N"], 4) % 1,
            }
            for m in find_local_minima(rows, window=3)
        ],
    }
    out_path = "results/density_insight.json"
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()