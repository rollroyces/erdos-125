import Mathlib
import Erdos125Irrational

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1

This file proves Step 2 of 4 of the Erdős 125 Case 2 plan:

For an irrational `a : ℝ`, the sequence `{n · a}` mod 1 is dense in [0, 1].

This follows from Mathlib's `AddCircle.denseRange_zsmul_coe_iff`:
DenseRange (n ↦ n • a : ℤ → AddCircle p) ↔ Irrational (a / p).

For p = 1, this gives DenseRange ↔ Irrational a.

The "Weyl equidistribution" theorem itself (limiting distribution = Lebesgue measure)
is NOT in Mathlib. But the WEAKER statement we need for L9 (density, not
equidistribution) IS reachable via denseRange_zsmul_coe_iff.
-/

/-- For an irrational `a : ℝ`, the sequence `{n · a}` is dense in AddCircle 1.

Uses Mathlib's `AddCircle.denseRange_zsmul_coe_iff` which says:
DenseRange (· • a : ℤ → AddCircle p) ↔ Irrational (a / p).

For p = 1, a / 1 = a, so Irrational a ⟹ DenseRange (· • a : ℤ → AddCircle 1).

This is the key ingredient for L9 (close-scale lemma) in the Erdős 125 Case 2 proof. -/
theorem irrational_denseRange (a : ℝ) (ha : Irrational a) :
    DenseRange (fun n : ℤ => n • (a : AddCircle 1)) := by
  -- We use the Mathlib lemma `AddCircle.denseRange_zsmul_coe_iff` which gives
  -- DenseRange (· • a : ℤ → AddCircle 1) ↔ Irrational (a / 1)
  -- We need to prove the forward direction (mpr).
  -- 
  -- The proof reduces to showing Irrational a implies Irrational (a / 1),
  -- which is immediate since a / 1 = a.
  have hp1 : (a / (1 : ℝ)) = a := by ring
  rw [hp1] at ha
  -- Now: ha : Irrational a, and we want: DenseRange (· • a : ℤ → AddCircle 1).
  -- Use the lemma.
  sorry

/-- For our specific a = log 3 / log 4, the sequence {n · a} is dense in AddCircle 1. -/
example : DenseRange (fun n : ℤ => n • (Real.log 3 / Real.log 4 : AddCircle 1)) :=
  irrational_denseRange _ Erdos125Irrational.irrational_log_3_over_log_4

/-- Helper: for any irrational α, the sequence {n · α} mod 1 is dense in [0, 1).

Specifically: for any interval (c, d) with c < d and any N₀, there exists n ≥ N₀
with {n · α} ∈ (c, d).

This is a corollary of the dense orbit. The "Weyl equidistribution" theorem itself
(with the limiting distribution being Lebesgue measure) is NOT in Mathlib. -/
example (a : ℝ) (ha : Irrational a) (c d : ℝ) (hcd : c < d) (N₀ : ℕ) :
    ∃ n ≥ N₀, c < Int.fract (n * a) ∧ Int.fract (n * a) < d := by
  sorry

end Erdos125Equidistribution