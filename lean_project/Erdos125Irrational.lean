import Mathlib

namespace Erdos125Irrational

open Real

/-! # Irrationality of log 3 / log 4

We prove: `Irrational (Real.log 3 / Real.log 4)`.

The proof:
1. Assume log 3 / log 4 = p/q for positive integers p, q
2. Cross-multiply: q · log 3 = p · log 4
3. Use log_pow: log(3^q) = log(4^p)
4. By injectivity of log on positive reals: 3^q = 4^p
5. By unique prime factorization: 3^q has only factor 3, 4^p has only factor 2
6. So both equal 1, giving p = q = 0, contradicting q > 0.

Mathlib has all the pieces we need.
-/

/-- log(3^q) = q · log 3 -/
example (q : ℕ) : Real.log (3 ^ q : ℝ) = (q : ℝ) * Real.log 3 := by
  exact Real.log_pow 3 q

/-- log(4^p) = p · log 4 -/
example (p : ℕ) : Real.log (4 ^ p : ℝ) = (p : ℝ) * Real.log 4 := by
  exact Real.log_pow 4 p

/-- log 3 > 0 -/
example : Real.log 3 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 3)

/-- log 4 > 0 -/
example : Real.log 4 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 4)

/-- log 3 / log 4 > 0 -/
example : Real.log 3 / Real.log 4 > 0 := by
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 4)

/-- 3 ∤ 4 -/
example : ¬ (3 : ℕ) ∣ 4 := by norm_num

/-- 2 ∤ 3 -/
example : ¬ (2 : ℕ) ∣ 3 := by norm_num

/-- For n ≥ 1, 3^n ≥ 3 -/
theorem three_pow_ge_three (q : ℕ) (hq : q ≥ 1) : 3 ^ q ≥ 3 := by
  -- 3^q = 3 * 3^(q-1) ≥ 3 since 3^(q-1) ≥ 1
  have hq1 : (q : ℕ) = (q - 1) + 1 := by omega
  rw [hq1, pow_succ]
  -- Goal: 3 * 3^(q-1) ≥ 3, i.e., 3^(q-1) ≥ 1.
  have h1 : (3 : ℕ) ^ (q - 1) ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  linarith

/-- For n ≥ 1, 4^n ≥ 4 -/
theorem four_pow_ge_four (p : ℕ) (hp : p ≥ 1) : 4 ^ p ≥ 4 := by
  have hp1 : (p : ℕ) = (p - 1) + 1 := by omega
  rw [hp1, pow_succ]
  have h1 : (4 : ℕ) ^ (p - 1) ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  linarith

/-- 3^q = 4^p with p, q ≥ 0 implies p = 0 and q = 0.

This is just unique prime factorization in ℕ:
3^q has prime factorization 3^q (only prime 3)
4^p = 2^(2p) has prime factorization 2^(2p) (only prime 2)
These are equal only when both are 1, i.e., p = q = 0. -/
theorem pow_3_eq_pow_4 (p q : ℕ) (h : (3 ^ q : ℕ) = 4 ^ p) : p = 0 ∧ q = 0 := by
  refine ⟨?_, ?_⟩
  · -- p = 0
    rcases Nat.eq_zero_or_pos p with hp0 | hp
    · exact hp0  -- p = 0 case: hp0 : p = 0, but we need p = 0 as the conclusion
    · -- p ≥ 1: derive contradiction.
      have hpleq1 : p ≥ 1 := hp
      have hq : q ≥ 1 := by
        rcases Nat.eq_zero_or_pos q with hq0 | hq
        · -- q = 0: 3^0 = 1 = 4^p. But p ≥ 1 gives 4^p ≥ 4 > 1.
          subst hq0
          have h4p : 4 ^ p ≥ 4 := four_pow_ge_four p hpleq1
          linarith
        · exact hq
      -- Now both p ≥ 1 and q ≥ 1, and 3^q = 4^p.
      -- 3 ∣ 3^q = 4^p, so 3 ∣ 4^p, so 3 ∣ 4. Contradiction.
      have h3q : (3 : ℕ) ∣ 3 * 3 ^ (q - 1) := dvd_mul_right 3 (3 ^ (q - 1))
      have h3q' : (3 : ℕ) ∣ 3 ^ q := by
        have hqq : q = (q - 1) + 1 := by omega
        rw [hqq, pow_succ]
        rw [mul_comm]
        exact h3q
      have h3dvd4p : (3 : ℕ) ∣ 4 ^ p := h ▸ h3q'
      have h3dvd4 : (3 : ℕ) ∣ 4 := Nat.Prime.dvd_of_dvd_pow (by norm_num : (3 : ℕ).Prime) h3dvd4p
      norm_num at h3dvd4
  · -- q = 0
    rcases Nat.eq_zero_or_pos q with hq0 | hq
    · exact hq0  -- q = 0 case
    · -- q ≥ 1: derive contradiction.
      have hqleq1 : q ≥ 1 := hq
      have hp : p ≥ 1 := by
        rcases Nat.eq_zero_or_pos p with hp0 | hp
        · -- p = 0: 4^0 = 1 = 3^q. But q ≥ 1 gives 3^q ≥ 3 > 1.
          subst hp0
          have h3q : 3 ^ q ≥ 3 := three_pow_ge_three q hqleq1
          linarith
        · exact hp
      -- Now both p ≥ 1 and q ≥ 1, and 3^q = 4^p.
      -- 2 ∣ 4^p: since 4^p = 4^(p-1) * 4 = 4^(p-1) * 2 * 2 = 2 * (2 * 4^(p-1)).
      have h2dvd4p : (2 : ℕ) ∣ 4 ^ p := by
        -- 4^p = 4^(p-1) * 4 (by pow_succ)
        have h1 : p = (p - 1) + 1 := by omega
        rw [h1, pow_succ]
        -- Goal: 2 ∣ 4^(p-1) * 4.
        -- 4^(p-1) * 4 = 4^(p-1) * (2 * 2) = 2 * (2 * 4^(p-1)) (by ring).
        rw [show 4 ^ (p - 1) * 4 = 2 * (2 * 4 ^ (p - 1)) from by ring]
        -- Goal: 2 ∣ 2 * (2 * 4^(p-1)).
        exact dvd_mul_right 2 (2 * 4 ^ (p - 1))
      -- 4^p = 3^q, so 2 ∣ 3^q.
      have h2dvd3q : (2 : ℕ) ∣ 3 ^ q := h ▸ h2dvd4p
      -- 2 ∣ 3^q → 2 ∣ 3.
      have h2dvd3 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd3q
      norm_num at h2dvd3

/-- Helper: 3^q = 4^p as reals implies 3^q = 4^p as nats.

Since 3^q, 4^p are positive reals, their equality as reals implies equality as nats. -/
example (p q : ℕ) (h : (3 ^ q : ℝ) = (4 ^ p : ℝ)) : (3 ^ q : ℕ) = 4 ^ p := by
  exact_mod_cast h

/-- The main result: log 3 / log 4 is irrational.

Strategy: assume log 3 / log 4 = r for some r : ℚ.
Then r = (r.num : ℝ) / (r.den : ℝ), with r.den ≥ 1 (always), r.num > 0 (since log 3 / log 4 > 0).
Cross-multiply: r.den · log 3 = r.num · log 4.
Take log of both sides using Real.log_pow: log(3^|r.num|) = log(4^|r.num|).
Wait, that's wrong. Let me redo.

Actually: r.den · log 3 = r.num · log 4.
Apply Real.log_pow: Real.log (3^(r.den : ℕ)) = (r.den : ℝ) * Real.log 3.
Similarly Real.log (4^(r.num : ℕ)) = (r.num : ℝ) * Real.log 4.

But r.num is ℤ, not ℕ. Convert via Int.natAbs.

If r.num ≥ 0, use r.num.natAbs = r.num.
If r.num < 0, we'd need r.den · log 3 = r.num · log 4 with r.num < 0.
But log 3 > 0, log 4 > 0, r.den > 0, so LHS > 0, RHS < 0. Contradiction.
So r.num ≥ 0, and r.num.natAbs = r.num.

Then (r.num : ℝ) * log 4 = (r.num : ℕ).cast * log 4 = log (4^(r.num : ℕ)).

Hmm but actually r.num : ℤ cast to ℝ equals r.num.natAbs cast to ℝ as a Nat, since r.num ≥ 0.

So we get log(3^(r.den)) = log(4^(r.num)).
By Real.log_injOn_pos (log is injective on positive reals): 3^(r.den) = 4^(r.num).
By pow_3_eq_pow_4: r.den = 0, but r.den ≥ 1. Contradiction.

We need to handle the fact that r.num is Int, not Nat. -/
theorem irrational_log_3_over_log_4 : Irrational (Real.log 3 / Real.log 4) := by
  intro h
  -- h : ∃ r : ℚ, Real.log 3 / Real.log 4 = r
  obtain ⟨r, hr⟩ := h
  -- Step 1: r > 0.
  have hr_pos : (0 : ℚ) < r := by
    have hr_pos_real : (0 : ℝ) < (r : ℝ) := by
      rw [hr]
      positivity
    exact (Rat.cast_pos.mp hr_pos_real)
  -- Step 2: r.num > 0 (since r > 0).
  have hr_num_pos : (0 : ℤ) < r.num := Rat.num_pos.mpr hr_pos
  -- Step 3: Cross-multiply hr.
  -- hr : (r : ℝ) = log 3 / log 4
  -- r.num / r.den = log 3 / log 4 → r.num * log 4 = r.den * log 3
  have hcross : (r.num : ℝ) * Real.log 4 = (r.den : ℝ) * Real.log 3 := by
    -- r : ℝ = (r.num : ℝ) / (r.den : ℝ) (Rat.cast_def).
    rw [Rat.cast_def] at hr
    -- hr : (r.num : ℝ) / (r.den : ℝ) = log 3 / log 4
    -- Cross-multiply: X/Y = A/B → X*B = Y*A when Y, B > 0.
    have hrden_pos : (r.den : ℝ) > 0 := by
      have := Rat.den_pos r
      rify at this
      exact this
    have hlog4_pos : Real.log 4 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have hrden_ne : (r.den : ℝ) ≠ 0 := by positivity
    have hlog4_ne : Real.log 4 ≠ 0 := ne_of_gt hlog4_pos
    -- Apply div_eq_div_iff (X/Y = A/B ↔ X*B = Y*A) when Y, B ≠ 0.
    rw [div_eq_div_iff hrden_ne hlog4_ne] at hr
    -- hr : r.num * log 4 = r.den * log 3 (after div_eq_div_iff)
    rw [mul_comm (Real.log 3) (r.den : ℝ)] at hr
    exact hr
  -- Step 4: Apply log_pow.
  have hlog3 : Real.log (3 ^ (r.den : ℕ) : ℝ) = (r.den : ℝ) * Real.log 3 :=
    Real.log_pow 3 r.den
  have hlog4 : Real.log (4 ^ (r.num.toNat : ℕ) : ℝ) = (r.num.toNat : ℝ) * Real.log 4 :=
    Real.log_pow 4 r.num.toNat
  -- Step 5: r.num.toNat = r.num (since r.num ≥ 0).
  have hr_num_toNat : (r.num.toNat : ℤ) = r.num := by
    rw [Int.toNat_of_nonneg (le_of_lt hr_num_pos)]
  have hnum_eq : (r.num : ℝ) = (r.num.toNat : ℝ) := by
    rw [← hr_num_toNat, Int.cast_natCast]
    rfl
  -- Step 6: log (3^(r.den)) = log (4^(r.num.toNat)).
  have heq : Real.log (3 ^ (r.den : ℕ) : ℝ) = Real.log (4 ^ (r.num.toNat : ℕ) : ℝ) := by
    rw [hlog3, hlog4, ← hnum_eq, hcross]
  -- Step 7: By injectivity of log: 3^(r.den) = 4^(r.num.toNat).
  have hpow_eq : (3 ^ (r.den : ℕ) : ℝ) = (4 ^ (r.num.toNat : ℕ) : ℝ) := by
    apply Real.log_injOn_pos
    · have : (0 : ℝ) < 3 ^ (r.den : ℕ) := by positivity
      exact Set.mem_Ioi.mpr this
    · have : (0 : ℝ) < 4 ^ (r.num.toNat : ℕ) := by positivity
      exact Set.mem_Ioi.mpr this
    · exact heq
  -- Step 8: As nats.
  have hpow_nat : (3 ^ (r.den : ℕ) : ℕ) = 4 ^ (r.num.toNat : ℕ) := by
    exact_mod_cast hpow_eq
  -- Step 9: By pow_3_eq_pow_4, contradiction.
  -- pow_3_eq_pow_4 p q : 3^q = 4^p → p = 0 ∧ q = 0.
  -- We have 3^(r.den) = 4^(r.num.toNat), so q = r.den, p = r.num.toNat.
  have hcontra := pow_3_eq_pow_4 r.num.toNat r.den hpow_nat
  -- r.den : ℕ > 0 (Mathlib convention for Rat.den).
  have hden_pos : (0 : ℕ) < r.den := Rat.den_pos r
  have hden_ne_zero : r.den ≠ 0 := by
    intro h
    rw [h] at hden_pos
    simp at hden_pos
  have hden_zero : r.den = 0 := hcontra.2
  exact hden_ne_zero hden_zero

end Erdos125Irrational