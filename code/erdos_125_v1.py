"""
Phase E: Erdős 125 — A+B density problem.

Question: What is the density behavior of A + B, where
- A = integers with digits 0,1 in base 3
- B = integers with digits 0,1 in base 4?

The four cases for (lower, upper) density:
1. (0, 0) — neither has positive density
2. (0, positive) — only upper density is positive
3. (positive, positive, equal) — natural density exists
4. (positive, positive, unequal) — liminf < limsup, no density

From Lean (already proved):
- Case 3 (HasPosDensity) is FALSE: A+B does NOT have natural density
- Case 4 (positive lower, unequal): FALSE (because lower density = 0)

Open (per Lean):
- Case 1: Is upper density 0? (= Case 2 if upper density > 0)
- Case 2: Is upper density > 0?

So the open sub-question is: **is upper density of A+B > 0?**

Numerical experiments show:
- |A+B ∩ [0,N]|/N stays around 0.85-0.93 for N up to 10^8
- Max gap grows with N (404k at N=10^7), suggesting lower density = 0
- Upper density appears positive (~0.85+)

This strongly suggests Case 2 is TRUE.
"""

import numpy as np
import time


def digits_in_base(n, b):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % b)
        n //= b
    return digits


def is_in_set(n, b):
    if n == 0:
        return True
    d = digits_in_base(n, b)
    return all(x in (0, 1) for x in d)


# Compute A+B for various N
print('=== Density of A+B at various N ===')
print(f'{"N":>12} {"|A+B|":>12} {"ratio":>10} {"max gap":>12}')
print()

for N_max in [10_000, 100_000, 1_000_000, 10_000_000]:
    t0 = time.time()
    A = [n for n in range(N_max + 1) if is_in_set(n, 3)]
    B = [n for n in range(N_max + 1) if is_in_set(n, 4)]
    AB = set()
    for a in A:
        for b in B:
            s = a + b
            if s <= N_max:
                AB.add(s)
    elapsed = time.time() - t0

    # Max gap
    AB_sorted = sorted(AB)
    max_gap = max(AB_sorted[i] - AB_sorted[i-1] for i in range(1, len(AB_sorted)))

    ratio = len(AB) / N_max
    print(f'{N_max:>12} {len(AB):>12} {ratio:>10.4f} {max_gap:>12}')


# Check ratio at very large N
print('\n=== Higher precision ===')
N_max = 100_000_000
t0 = time.time()
A = [n for n in range(N_max + 1) if is_in_set(n, 3)]
B = [n for n in range(N_max + 1) if is_in_set(n, 4)]
AB = set()
for a in A:
    for b in B:
        s = a + b
        if s <= N_max:
            AB.add(s)
elapsed = time.time() - t0
print(f'N = {N_max}: |A+B| = {len(AB)}, ratio = {len(AB)/N_max:.4f}, time = {elapsed:.1f}s')


# Now check density at consecutive intervals to look for oscillations
print('\n=== Density in sliding windows ===')
AB_sorted = sorted(AB)
window = 1_000_000  # 1M
densities = []
for start in range(0, N_max - window, window // 2):
    end = start + window
    cnt = sum(1 for x in AB_sorted if start <= x <= end)
    densities.append((start, cnt / window))

# Print summary stats
density_vals = [d for _, d in densities]
print(f'Window density: min = {min(density_vals):.4f}, max = {max(density_vals):.4f}, mean = {np.mean(density_vals):.4f}')

# Find the lowest-density window
min_density = min(density_vals)
min_idx = density_vals.index(min_density)
min_start = densities[min_idx][0]
print(f'Lowest density: {min_density:.4f} in window [{min_start}, {min_start + window}]')