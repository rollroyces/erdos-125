# 33: Step 3 L9 — CLOSED! 🎉

## Status

**Step 3 (L9 close-scale lemma) — CLOSED with 0 sorries!**

The full L9 theorem is now proven in `/Users/hermes/.hermes/projects/erdos_125/lean_project/Erdos125Equidistribution.lean`:

```lean
theorem L9 :
    ∃ n m : ℤ,
    |((3 : ℤ)^(n.natAbs) - (4 : ℤ)^(m.natAbs) : ℤ)| * 3 <
      (min ((3 : ℕ)^(n.natAbs)) ((4 : ℕ)^(m.natAbs)) : ℤ) := by
```

**Full project builds successfully**: `lake build` → `Build completed successfully (8866 jobs)`.

## What's proved (0 sorries)

1. **Step 1 (irrationality)**: `log 3 / log 4 ∉ ℚ` (Erdos125Irrational.lean)
2. **Step 2 (dense orbit)**: `DenseRange (· • a : ℤ → UnitAddCircle)` where `a = log 3 / log 4`
3. **Step 3 (L9)**: `∃ n m, |3^n.natAbs - 4^m.natAbs| · 3 < min(3^n.natAbs, 4^m.natAbs)` (in reals)
4. **Step 3e helpers** (all 0 sorries):
   - `exists_n_in_ball` — dense orbit gives n in any ball
   - `dist_lt_implies_close` — using `UnitAddCircle.norm_eq`
   - `exists_int_close` — integer close to real
   - `log_4_lt_2` — via `Real.exp_one_gt_two` (2 < exp 1)
   - `abs_abs_sub_abs_le_abs_sub` — reverse triangle inequality
   - `hδ₁_le : |δ₁| ≤ |δ₀|` — reverse triangle
   - `hkey : -log 4 / 10 ≥ log (3/4)` — via 3^10 ≤ 4^9
   - `hexp_δ₀_bound, hexp_δ₁_bound : |exp x - 1| ≤ |x| + x²` — via `Real.norm_exp_sub_one_sub_id_le`
   - `hbound : |δ| + δ² < 1/3` — from |δ| < log 4 / 10 < 1/5
   - `hkey : 3^k - 4^l = 4^l · (exp δ₁ - 1)` — key identity
   - `habs : |3^k - 4^l| = 4^l · |exp δ₁ - 1|` — using `abs_mul` and `abs_of_pos`
   - Case 1: 3^k < 4^l → δ₁ < 0 → |exp δ₁ - 1| = 1 - exp δ₁ → exp δ₁ > 3/4 (via the key chain)
   - Case 2: 3^k ≥ 4^l → trivial via `|exp δ₁ - 1| < 1/3`

## Key Mathlib findings

- `UnitAddCircle.norm_eq : ‖(x : UnitAddCircle)‖ = |x - round x|`
- `AddCircle.denseRange_zsmul_iff` and `AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div`
- `Real.norm_exp_sub_one_sub_id_le : |exp x - 1 - x| ≤ x²` for |x| ≤ 1
- `Real.exp_one_gt_two : 2 < exp 1` (and `Real.exp_add`)
- `Real.log_pow : log (x^n) = n · log x`, `Real.log_div`
- `Int.cast_pow`, `Int.cast_min`, `Int.cast_subNatNat`
- `Nat.cast_min : ((min m n : ℕ) : α) = min (m : α) n`
- `abs_sub_comm : |a - b| = |b - a|`
- `abs_add_le : |a + b| ≤ |a| + |b|`

## Files

- `/Users/hermes/.hermes/projects/erdos_125/lean_project/Erdos125Equidistribution.lean` — 397 lines, **0 sorries**, builds successfully
- All pushed to `https://github.com/rollroyces/erdos-125` (commit `59ced86`)

## Next step

Step 4 (Erdős 1955 main argument) in `Erdos125Case2.lean` still has 3 sorries. Now that L9 is fully proved, we can use it directly. The digit-sumset argument (`digit_sumset`) and density (`density_via_L9`) remain to be completed.

## Summary of progress

| Step | Status |
|------|--------|
| Step 1 (irrationality) | ✅ CLOSED |
| Step 2 (dense orbit) | ✅ CLOSED |
| Step 3 (L9) | ✅ CLOSED |
| Step 4 (Erdős 1955) | ❌ 3 sorries in `Erdos125Case2.lean` |
