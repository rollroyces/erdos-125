# 40: Step 4 Major Breakthrough — Closed 2 Sorries

## What I closed

Closed the following sorries in `Erdos125A.lean`:

1. `decomp_a1_aux_inA` (was sorry)
2. `decomp_a2_aux_inA` (was sorry)

## Key proofs added

- `decomp_a1_aux_eq`, `decomp_a2_aux_eq`: `decomp_aN_aux n k = 3^k * decomp_aN_aux n 0`
- `inA_mul_three`: `inA (3n) = true` when `inA n = true` (strong induction)
- `inA_mul_three_pow`: `inA (3^k * n) = true` when `inA n = true`
- `inA_3a_plus_c`: `inA (3a + c) = true` when `a ∈ A`, `c ∈ {0, 1}`
- `decomp_a1_aux_0_inA`, `decomp_a2_aux_0_inA`: the k=0 base cases
- `decomp_a1_aux_inA`, `decomp_a2_aux_inA`: **CLOSED** using the above

## Current state of project

| File | Active sorries |
|------|----------------|
| `Erdos125A.lean` | 1 (`decomp_a1_sum`, pre-existing) |
| `Erdos125Case2.lean` | 2 (`digit_sumset` line 71, `density_via_L9` line 103) |
| All other 12 files | 0 |
| **Total** | **3 active sorries** |

## What remains

`density_via_L9` line 103 (N₀ ≥ 65536 case): requires either
- Self-similarity lemma, or
- Larger `native_decide` examples (>30 min compute)

## What works

- `erdos_125_case_2_positive_density` ✅ CLOSED for N₀ < 65536
- `decomp_a1_aux_inA`, `decomp_a2_aux_inA` ✅ CLOSED
- Full project builds (8866 jobs)

## Pushed

Commit `c4da8b9` to `origin/main`.
