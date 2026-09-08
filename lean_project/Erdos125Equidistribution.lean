import Mathlib
import Erdos125Irrational
import Mathlib.Topology.Instances.AddCircle.Real

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1 (Step 2)

This file proves Step 2 of the Erdős 125 Case 2 plan: the dense orbit
{n · log 3 / log 4} mod 1 is dense in the unit circle [0, 1).

This is the WEAKER statement than Weyl equidistribution (which gives the
limiting distribution as Lebesgue measure), but it's sufficient for L9.

The proof uses Mathlib's `AddCircle.denseRange_zsmul_iff`:
DenseRange (· • a : ℤ → AddCircle p) ↔ addOrderOf a = 0.

Applied to a := QuotientAddGroup.mk (log 3 / log 4) in AddCircle 1 (= UnitAddCircle).

Combined with `Erdos125Irrational.irrational_log_3_over_log_4`, this gives the dense orbit.

## Step 3 (L9) — close-scale lemma

For every N₀, there exist k, m with min(3^k, 4^m) > N₀ and
|3^k - 4^m| / min(3^k, 4^m) < 1/3.

The proof uses the dense orbit: since {k · log 3 / log 4} mod 1 is dense,
we can find k with {k · log 3 / log 4} close to 0. Then m = round(k · log 3 / log 4)
gives the close-scale.
-/

/-- Lift log 3 / log 4 to UnitAddCircle. -/
noncomputable def a : UnitAddCircle := QuotientAddGroup.mk (Real.log 3 / Real.log 4)

/-- **Step 2: Dense orbit.**

For our specific a = log 3 / log 4, the sequence {n · a} mod 1 is dense in UnitAddCircle.

Uses Mathlib's `AddCircle.denseRange_zsmul_iff`:
DenseRange (· • a : ℤ → AddCircle p) ↔ addOrderOf a = 0.

Then uses `AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div` to show
¬ IsOfFinAddOrder a, which follows from the irrationality of log 3 / log 4.

This is the main result of Step 2 of the Erdős 125 Case 2 plan. -/
theorem dense_orbit_log_3_over_log_4 :
    DenseRange (· • a : ℤ → UnitAddCircle) := by
  -- Apply AddCircle.denseRange_zsmul_iff to convert DenseRange ↔ addOrderOf a = 0
  rw [AddCircle.denseRange_zsmul_iff]
  -- Need: addOrderOf a = 0
  rw [addOrderOf_eq_zero_iff]
  -- Need: ¬ IsOfFinAddOrder a
  -- Use the lemma isOfFinAddOrder_iff_exists_rat_eq_div specialized to a := log 3 / log 4, p := 1.
  have h_iff := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div
    (p := (1 : ℝ)) (a := (Real.log 3 / Real.log 4))
  -- h_iff : IsOfFinAddOrder ↑(log 3 / log 4) ↔ ∃ q : ℚ, (q : ℝ) = log 3 / log 4 / 1
  -- Note a = ↑(log 3 / log 4)
  show ¬ IsOfFinAddOrder a
  have ha : a = ↑(Real.log 3 / Real.log 4) := rfl
  rw [ha]
  -- Now: ¬ IsOfFinAddOrder ↑(log 3 / log 4)
  -- Use h_iff.mp to derive a rational witness, contradicting irrationality.
  intro hcontra
  obtain ⟨q, hq⟩ := h_iff.mp hcontra
  -- hq : (q : ℝ) = (log 3 / log 4) / 1
  rw [div_one] at hq
  -- hq : (q : ℝ) = log 3 / log 4
  -- Contradiction with Erdos125Irrational.irrational_log_3_over_log_4
  have hirr := Erdos125Irrational.irrational_log_3_over_log_4
  -- Need to convert hq : ↑q = log 3 / log 4 to log 3 / log 4 ∈ Set.range Rat.cast
  have : Real.log 3 / Real.log 4 ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, hq⟩
  exact hirr this

/-- **Step 3: L9 (close-scale lemma)** — formal statement.

For every N₀ : ℕ, there exist k, m : ℕ with min (3^k) (4^m) > N₀ and
|3^k - 4^m| < (min (3^k) (4^m)) / 3.

The proof uses the dense orbit from Step 2:
- Since the sequence {k · log 3 / log 4} mod 1 is dense in [0, 1], for any ε > 0,
  there exist k with {k · log 3 / log 4} < ε.
- Set m = round(k · log 3 / log 4). Then |k · log 3 / log 4 - m| = {k · log 3 / log 4} < ε.
- Exponentiating: 3^k ≈ 4^m (with relative error < ε · |log 4|).
- In particular, for ε < 1/(3 · log 4), we get |3^k - 4^m| / 4^m < 1/3.

The formalization of this last step requires bounding |e^x - 1| from |x| in terms of ε. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  sorry

end Erdos125Equidistribution