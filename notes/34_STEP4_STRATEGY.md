# 34: Step 4 Strategy (Erdős 1955)

## Goal

Close the 3 remaining sorries in `Erdos125Case2.lean`:
1. `digit_sumset` (line 74)
2. `density_via_L9` (line 83)
3. `erdos_125_case_2_positive_density` (line 88)

## Approach: Erdős 1955 self-similarity

The full formal digit-sumset argument (digit-level no-carry decomposition) is complex. We use a cleaner approach based on the structural properties:

**Key fact (self-similarity)**: For any N = 4^m, the structure of A ∩ [0, N) and B ∩ [0, N) is preserved under scaling by 4 (modulo shifts). Specifically:
- A ∩ [4^m, 2·4^m) corresponds to A shifted by 4^m
- B ∩ [4^m, 2·4^m) has the same structure as B (up to shift)

**Density self-similarity**: `countAB_in_0_N (4^(m+1)) ≥ 2 · countAB_in_0_N (4^m)`.

This is because pairs (a, b) ∈ A × B with a + b < 4^m contribute to sums in [0, 4^m), and pairs with 4^m ≤ a + b < 2·4^m contribute to sums in [4^m, 2·4^m). The number of pairs in each case is approximately equal.

**Erdős 1955 argument**: For all n with 0 ≤ n < 4^m, n = a + b with a ∈ A, b ∈ B exists for almost all n (specifically, n ≤ 3^k + 4^m - 1 where 3^k ≈ 4^m by L9).

## Concrete plan

1. **digit_sumset**: Leave as sorry with clear comment. Not directly used.

2. **density_via_L9**: 
   - For N₀ < 4^5 = 1024, verify density at concrete m = 5, 6, 7, 8 via `native_decide`.
   - For N₀ ≥ 4^8 = 65536, use the self-similarity argument:
     - countAB_in_0_N (4^m) ≥ 2^((m - m₀)) · countAB_in_0_N (4^m₀) for any m ≥ m₀.
   - This gives density > 1/2 for all large enough m.

3. **erdos_125_case_2_positive_density**: Apply density_via_L9 with k chosen via L9 (or just pick m with 4^m > N₀ directly).

## Key insight

The L9 lemma (Step 3) is **not strictly needed** for the positive density result. We just need density > 1/2 at ONE concrete large N, and the self-similarity extends it to all larger N. L9's role is to ensure we have density > 1/2 at N = 4^m where 3^k ≈ 4^m.

## Numerical verification

The existing `Erdos125Density.lean` has verified `countAB_in_0_N (4^m) > 4^m / 2` for m ∈ {1, 2, 3, 4, 5, 6, 7} via `native_decide`. This gives us a concrete base case.

## Status: WIP

Build currently in progress (Mathlib rebuild). Will close sorries once build completes.
