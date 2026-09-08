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

/-- Helper: from `dist (↑x) 0 < 1/2`, get a real number m with |x - m| < 1/2. -/
lemma exists_int_close (x : ℝ) (h : (↑x : UnitAddCircle) ∈ Metric.ball 0 (1/2)) :
    ∃ m : ℤ, |x - m| < 1/2 := by
  refine ⟨round x, ?_⟩
  exact dist_lt_implies_close x h

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
6. Choose ε small enough that (ε · log 4)^2 < 1/3, e.g., ε = 0.4/log 4. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  sorry
end Erdos125Equidistribution