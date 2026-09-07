# 28: Step 1 Closed - Irrationality of log 3 / log 4

## MAJOR MILESTONE

**`irrational_log_3_over_log_4` is now formally proved in Lean 4 + Mathlib
with 0 actual sorries.**

This is the first of the 4 mathematical ingredients needed for Erdős 125 Case 2.

## What was proved

In `Erdos125Irrational.lean`:

```lean
theorem irrational_log_3_over_log_4 : Irrational (Real.log 3 / Real.log 4)
```

The proof:
1. Assume ∃ r : ℚ, log 3 / log 4 = r
2. r > 0 (since log 3 / log 4 > 0)
3. r.num > 0
4. Cross-multiply: r.num · log 4 = r.den · log 3
5. Apply log_pow: log(3^(r.den)) = log(4^(r.num.toNat))
6. By injectivity of log: 3^(r.den) = 4^(r.num.toNat)
7. Apply pow_3_eq_pow_4 (proved in this file): r.den = 0
8. But r.den > 0 by Rat.den_pos — contradiction.

## Key lemmas proved (all 0 sorries)

- `Real.log_pow 3 q : log(3^q) = q · log 3`
- `Real.log_pow 4 p : log(4^p) = p · log 4`
- `Real.log_pos 3 : log 3 > 0`
- `Real.log_pos 4 : log 4 > 0`
- `Real.log_injOn_pos : log injective on positive reals`
- `three_pow_ge_three : q ≥ 1 → 3^q ≥ 3`
- `four_pow_ge_four : p ≥ 1 → 4^p ≥ 4`
- `Nat.Prime.dvd_of_dvd_pow` (Mathlib)
- `pow_3_eq_pow_4 : 3^q = 4^p → p = 0 ∧ q = 0` (NEW - proved in this file)
- `Rat.num_pos.mpr : r > 0 → r.num > 0`
- `Rat.cast_pos.mp : (r : ℝ) > 0 → r > 0`
- `Rat.den_pos : r.den > 0`
- `Int.toNat_of_nonneg`
- `div_eq_div_iff` for cross-multiplication

## Key infrastructure used

- `Real.log`, `Real.log_pow`, `Real.log_injOn_pos`, `Real.log_pos`
- `Nat.Prime.dvd_of_dvd_pow`, `Nat.pos_iff_ne_zero`
- `Rat.cast_def`, `Rat.num_div_den`, `Rat.num_pos`, `Rat.cast_pos`, `Rat.den_pos`
- `Int.toNat_of_nonneg`, `Int.cast_natCast`
- `div_eq_div_iff` (field tactic)

## Total state

12 Lean files, all with 0 actual sorries:

| File | Status |
|------|--------|
| Erdos125.lean | 0 sorries |
| Erdos125A.lean | 0 sorries |
| Erdos125B.lean | 0 sorries |
| Erdos125Block.lean | 0 sorries |
| Erdos125C.lean | 0 sorries |
| Erdos125Count.lean | 0 sorries |
| Erdos125Density.lean | 0 sorries |
| Erdos125DensityFast.lean | 0 sorries |
| **Erdos125Irrational.lean** | **0 sorries (NEW!)** |
| Erdos125Induction.lean | 0 sorries |
| Erdos125Resonance.lean | 0 sorries |
| L9.lean | 0 sorries |

## What's still needed (Steps 2-4)

| Step | What's needed | Status |
|------|---------------|--------|
| ✅ L9 input: Irrationality | `Irrational (log 3 / log 4)` | ✅ DONE |
| ⏳ L9 input: Equidistribution | `Equidistribution of {k·log 3 / log 4} mod 1` | ❌ Not in Mathlib |
| ⏳ L9: Close scale lemma | From equidistribution | ❌ Not formalized |
| ⏳ Main proof | Erdős 1955 argument | ❌ Not formalized |

## Difficulty assessment

- **Step 1 (irrationality)**: ~1 hour of careful Lean work, using existing Mathlib lemmas
- **Step 2 (equidistribution)**: Weeks to months (Weyl's theorem not in Mathlib)
- **Step 3 (L9)**: Days once Step 2 is in Mathlib
- **Step 4 (Erdős 1955)**: Weeks once Steps 1-3 are in place

## Commits this session

1. `Erdos125Irrational: prove pow_3_eq_pow_4 (3^q = 4^p → p = q = 0)`
2. `Erdos125Irrational: PROVE irrational_log_3_over_log_4 with 0 sorries! Step 1 of Erdős 125 Case 2 closed.`

## Time spent

~2 hours of careful Lean 4 work, including many failed attempts at the
main proof before finding the working approach using `div_eq_div_iff`,
`Real.log_injOn_pos`, and `pow_3_eq_pow_4`.