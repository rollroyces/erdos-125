# 31: Step 3 L9 — Major Progress, 1 Sorry Remaining

## Status

Step 2 (Dense orbit) — **CLOSED with 0 sorries** (previous batch).

Step 3 (L9 close-scale lemma) — **Major progress**, 1 sorry remaining.

## What's proved

In `Erdos125Equidistribution.lean`:

1. **`dense_orbit_log_3_over_log_4`** (0 sorries) — proven using:
   - `AddCircle.denseRange_zsmul_iff` (from `Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean`)
   - `AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div` (from same module)
   - `Erdos125Irrational.irrational_log_3_over_log_4`

2. **`exists_n_in_ball`** (0 sorries) — immediate from `DenseRange.exists_mem_open`

3. **`dist_lt_implies_close`** (0 sorries) — using `UnitAddCircle.norm_eq`:
   `‖(x : UnitAddCircle)‖ = |x - round x|`

4. **`exists_int_close`** (0 sorries) — wrapper around `dist_lt_implies_close`

5. **`L9`** — partial proof:
   - 3a: Find n with dist (n • a) 0 < 1/10  ✓
   - 3b: Apply `AddCircle.coe_zsmul` to lift to reals  ✓
   - 3c: Get integer m with |n · (log 3 / log 4) - m| < 1/10  ✓
   - 3d: Multiply through by log 4: |n log 3 - m log 4| < log 4 / 10  ✓
   - 3e: **Apply exp_bound** — ❌ sorry

## The remaining sorry

In Step 3e, I need to:

1. Set δ := (↑n : ℝ) * log 3 - (↑m : ℝ) * log 4.
2. We have |δ| < log 4 / 10 < 1.
3. Apply `Real.norm_exp_sub_one_sub_id_le : ‖exp δ - 1 - δ‖ ≤ ‖δ‖^2` (which gives
   |exp δ - 1| ≤ |δ| + δ²).
4. Show: |δ| + |δ|² < 1/3, i.e., log 4 / 10 + (log 4)² / 100 < 1/3.
5. Convert back to 3^↑n vs 4^↑m to get the L9 conclusion.

The numeric inequality (4) requires bounding log 4 since log 4 is irrational:
- log 4 < 1.4 (since exp 1.4 = 4.055... > 4)
- So |δ| + δ² < 1.4/10 + 1.96/100 = 0.14 + 0.0196 = 0.1596 < 0.333

This is achievable with `Real.log_lt_log` and `Real.log 4 < Real.exp (7/5) = exp 1.4`.

## Difficulty of the remaining step

- `Real.norm_exp_sub_one_sub_id_le` is in Mathlib at `Mathlib/Analysis/Complex/Exponential.lean:447`.
- The numeric inequality is real-arithmetic and should be straightforward with linarith/nlinarith.

I attempted this and ran into:
- Typeclass elaboration issues with `Real.log 4 < 2` etc.
- The exact bound `log 4 < exp(7/5)` needs explicit lemmas.

## Files

- `/Users/hermes/.hermes/projects/erdos_125/lean_project/Erdos125Equidistribution.lean` — 96 lines, 1 sorry
- All pushed to https://github.com/rollroyces/erdos-125 (commit `623f234`)

## Next step

If you want to continue closing Step 3, the remaining work is:

```lean
-- After getting hm4 : |δ| < log 4 / 10
set δ : ℝ := (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4
-- Apply exp_bound
have hbound := Real.norm_exp_sub_one_sub_id_le (x := δ) ...
-- Convert to real abs
-- Numeric: log 4 < 1.39 (need this as a lemma)
-- Conclude |exp δ - 1| < 1/3
-- Translate back to |3^↑n - 4^↑m| < min / 3
-- Make k, m positive via Int.natAbs
```