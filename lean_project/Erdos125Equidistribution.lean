import Mathlib
import Erdos125Irrational
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1 (Step 2 + Step 3: L9)

Step 2: The dense orbit {n · log 3 / log 4} mod 1 is dense in the unit circle [0, 1).

Step 3 (L9): For every N₀, there exist k, m with min (3^k, 4^m) > N₀ and
|3^k - 4^m| · 3 < min (3^k, 4^m), i.e., |3^k - 4^m| < min (3^k, 4^m) / 3.

This is the close-scale lemma needed for Erdős 1955 Case 2.
-/

/-- Lift log 3 / log 4 to UnitAddCircle. -/
noncomputable def a : UnitAddCircle := QuotientAddGroup.mk (Real.log 3 / Real.log 4)

/-- **Step 2: Dense orbit.** -/
theorem dense_orbit_log_3_over_log_4 :
    DenseRange (· • a : ℤ → UnitAddCircle) := by
  rw [AddCircle.denseRange_zsmul_iff]
  rw [addOrderOf_eq_zero_iff]
  have h_iff := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div
    (p := (1 : ℝ)) (a := (Real.log 3 / Real.log 4))
  show ¬ IsOfFinAddOrder a
  have ha : a = ↑(Real.log 3 / Real.log 4) := rfl
  rw [ha]
  intro hcontra
  obtain ⟨q, hq⟩ := h_iff.mp hcontra
  rw [div_one] at hq
  have : Real.log 3 / Real.log 4 ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, hq⟩
  exact Erdos125Irrational.irrational_log_3_over_log_4 this

/-- Helper: for any 0 < ε, there exists n : ℤ such that the
(n-th) zsmul of a is within ε of 0 in UnitAddCircle. -/
lemma exists_n_in_ball (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℤ, (n • a : UnitAddCircle) ∈ Metric.ball 0 ε := by
  have h := dense_orbit_log_3_over_log_4
  exact h.exists_mem_open Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩

/-- **Helper: round-to-nearest-integer bridge**.

If dist (↑x : UnitAddCircle) 0 < 1/2, then |x - round x| < 1/2 < 1.

Proof: by UnitAddCircle.norm_eq, ‖(x : UnitAddCircle)‖ = |x - round x|.
And dist ↑x 0 = ‖↑x - 0‖ = ‖↑x‖. So dist ↑x 0 < 1/2 ↔ |x - round x| < 1/2. -/
lemma dist_lt_implies_close (x : ℝ) (h : (↑x : UnitAddCircle) ∈ Metric.ball 0 (1/2)) :
    |x - round x| < 1/2 := by
  rw [Metric.mem_ball, dist_eq_norm] at h
  -- h : ‖↑x - 0‖ < 1/2
  -- Convert ‖↑x - 0‖ to ‖↑x‖
  simp only [sub_zero] at h
  -- h : ‖↑x‖ < 1/2
  -- Apply UnitAddCircle.norm_eq
  rw [UnitAddCircle.norm_eq] at h
  exact h

/-- Helper: from `dist (↑x) 0 < ε`, get a real number m with |x - m| < ε. -/
lemma exists_int_close (x : ℝ) (ε : ℝ) (_hε : 0 < ε)
    (h : (↑x : UnitAddCircle) ∈ Metric.ball 0 ε) :
    ∃ m : ℤ, |x - m| < ε := by
  refine ⟨round x, ?_⟩
  -- Convert metric ball to norm bound
  have h' : |x - (round x : ℝ)| < ε := by
    rw [Metric.mem_ball, dist_eq_norm] at h
    simp only [sub_zero] at h
    rw [UnitAddCircle.norm_eq] at h
    -- Now h : |x - round x| < ε
    exact h
  exact h'

/-- **Step 3: L9 (close-scale lemma)**.

For every N₀ : ℕ, there exist k, m : ℕ with min (3^k, 4^m) > N₀ and
|3^k - 4^m| < min (3^k, 4^m) / 3.

Proof strategy:
1. Apply dense orbit: for small ε > 0, ∃ k : ℕ with dist (k • a) 0 < ε.
2. By norm_eq, |k · log 3 / log 4 - round (k · log 3 / log 4)| < ε.
3. Set m = round (k · log 3 / log 4). Then |k log 3 - m log 4| < ε · log 4.
4. Use exp_bound: |3^k - 4^m| ≤ 4^m · |exp((k log 3 - m log 4)) - 1|
                              ≤ 4^m · (ε · log 4)^2   (when ε · log 4 ≤ 1)
5. Combined: |3^k - 4^m| / 4^m ≤ (ε · log 4)^2.
6. Choose ε small enough that (ε · log 4)^2 < 1/3. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  -- Step 3a: Find n : ℤ with dist (n • a) 0 < 1/10
  obtain ⟨n, hn⟩ := exists_n_in_ball (1/10) (by norm_num)
  -- Step 3b: Use AddCircle.coe_zsmul to lift to real
  -- n • a = n • (QuotientAddGroup.mk (log 3 / log 4)) = QuotientAddGroup.mk (n • (log 3 / log 4))
  -- So we have ↑(n • (log 3 / log 4)) ∈ Metric.ball 0 (1/2)
  have hn' : (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) ∈ Metric.ball 0 (1/10) := by
    change (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) ∈ Metric.ball 0 (1/10) at hn
    have h : (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) =
             (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) := by
      rw [AddCircle.coe_zsmul (p := (1 : ℝ))]
    rw [h] at hn
    exact hn
  -- Step 3c: Get a real number m close to n • (log 3 / log 4)
  obtain ⟨m, hm⟩ := exists_int_close (n • (Real.log 3 / Real.log 4)) (1/10) (by norm_num) hn'
  -- hm : |n • (log 3 / log 4) - m| < 1/2
  -- Step 3d: Convert n • x to n * x (since n : ℤ)
  have hmul : (n • (Real.log 3 / Real.log 4)) = (n : ℝ) * (Real.log 3 / Real.log 4) := by
    rw [zsmul_eq_mul]
  rw [hmul] at hm
  -- hm : |↑n * (log 3 / log 4) - ↑m| < 1/10
  -- Multiply through by log 4: |↑n * log 3 - ↑m * log 4| < log 4 / 10
  have h4_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hm4 : |(↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4| < Real.log 4 / 10 := by
    have key : ((↑n : ℝ) * (Real.log 3 / Real.log 4) - (↑m : ℝ)) * Real.log 4 =
               (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4 := by field_simp
    rw [← key, abs_mul, abs_of_pos h4_pos]
    linarith [mul_lt_mul_of_pos_right hm h4_pos]
  -- Step 3e: Use exp_bound to convert log-distance to power-distance.
  -- For x ∈ ℝ with |x| ≤ 1, |exp(x) - 1 - x| ≤ x^2.
  -- Set δ := (n log 3 - m log 4). Then 3^n = 4^m * exp(δ).
  -- So 3^n - 4^m = 4^m * (exp(δ) - 1).
  -- We want: |3^n - 4^m| < 4^m / 3, i.e., |exp(δ) - 1| < 1/3.
  -- When |δ| ≤ 1, exp_bound gives |exp(δ) - 1 - δ| ≤ δ^2.
  -- So |exp(δ) - 1| ≤ |δ| + δ^2 ≤ 1/2 + 1/4 = 3/4. Not quite < 1/3.
  -- Need a tighter bound. Use |δ| < log 4 / 2 < 1, so |δ|^2 < log 4 / 4.
  -- Then |exp(δ) - 1| ≤ |δ| + |δ|^2 < log 4 / 2 + log 4 / 4 = 3 log 4 / 4 ≈ 1.04. Still too big.
  -- For |exp(δ) - 1| < 1/3, need |δ| + |δ|^2 < 1/3. Since log 4 ≈ 1.386, log 4 / 2 ≈ 0.693.
  -- We have |δ| < log 4 / 2 ≈ 0.693. Need: 0.693 + 0.480 ≈ 1.17 < 1/3. NO!
  -- Actually log 4 / 2 + (log 4 / 2)^2 = log 4 / 2 + log^2 4 / 4 ≈ 0.693 + 0.480 = 1.17.
  -- This is way bigger than 1/3. So our choice of 1/2 was too large.
  -- Need: |δ| < δ_max such that δ_max + δ_max^2 < 1/3, i.e., δ_max < ~0.27.
  -- So set ε = 1/2 in the original problem → |δ| < log 4 / 2 ≈ 0.693. Too big.
  -- Better: use ε = 1/3 in the dense orbit argument → |δ| < log 4 / 3 ≈ 0.462. Still too big.
  -- Need: ε = 0.25 → |δ| < log 4 / 4 ≈ 0.347, so |δ| + |δ|^2 < 0.347 + 0.120 ≈ 0.467. Still too big.
  -- Need: ε = 0.15 → |δ| < log 4 / 15 ≈ 0.0924, so |δ| + |δ|^2 < 0.0924 + 0.00854 ≈ 0.10. ✓ < 1/3!
  -- So we should use ε = 1/15 instead of 1/2.
  sorry
end Erdos125Equidistribution