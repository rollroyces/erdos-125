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

/-- Helper: for any 0 < ε < 1, there exists n ≥ 1 (positive integer) such that
Int.fract (n · (log 3 / log 4)) < ε.

This is the corollary of dense orbit that we need for L9. We use the
fact that the map n ↦ {n · a} (fractional part) is dense in [0, 1).

Specifically, we work with positive integers n : ℕ by considering n • a
where the add action on UnitAddCircle restricts to ℕ-action via the
canonical ℕ → ℤ inclusion. -/
lemma exists_n_small_fract (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, n > 0 ∧ Int.fract (n * (Real.log 3 / Real.log 4)) < ε := by
  sorry

/-- **Step 3: L9 (close-scale lemma)**.

For every N₀ : ℕ, there exist k, m : ℕ with min (3^k, 4^m) > N₀ and
|3^k - 4^m| < min (3^k, 4^m) / 3.

This is the close-scale lemma: we find k, m such that 3^k and 4^m are
relatively close (within 1/3 of the smaller).

Proof strategy:
1. Apply dense orbit: for small ε > 0, ∃ k with {k · log 3 / log 4} < ε.
2. Let m = floor(k · log 3 / log 4). Then |k · log 3 - m · log 4| < ε · log 4.
3. Use exp_bound: |3^k - 4^m| ≤ 4^m · |exp((k log 3 - m log 4)) - 1|
                              ≤ 4^m · (ε · log 4)^2   (when ε · log 4 ≤ 1)
4. Combined: |3^k - 4^m| / 4^m ≤ (ε · log 4)^2.
5. Choose ε small enough that (ε · log 4)^2 < 1/3, e.g., ε = 0.4/log 4. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  -- Step 3a: Find k > 0 with fract(k · log 3 / log 4) < small ε
  -- Step 3b: Set m = round(k · log 3 / log 4), so |k log 3 - m log 4| < ε log 4
  -- Step 3c: Bound |3^k - 4^m| / min(3^k, 4^m) using exp_bound
  sorry

end Erdos125Equidistribution