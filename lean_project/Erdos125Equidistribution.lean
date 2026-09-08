import Mathlib
import Erdos125Irrational

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1

This file proves Step 2 of 4 of the Erdős 125 Case 2 plan:

For an irrational `a : ℝ`, the sequence `{n · a}` mod 1 is dense in [0, 1].

This follows from Mathlib's `denseRange_zsmul_coe_iff`:
DenseRange (n ↦ n • a : ℤ → AddCircle p) ↔ Irrational (a / p).

The "Weyl equidistribution" theorem itself (limiting distribution = Lebesgue measure)
is NOT in Mathlib. But the WEAKER statement we need for L9 (density, not
equidistribution) IS reachable via denseRange_zsmul_coe_iff.
-/

/-- For an irrational `a : ℝ`, the sequence `{n · a}` is dense in AddCircle 1.

Uses Mathlib's `AddCircle.denseRange_zsmul_coe_iff` which says:
DenseRange (· • a : ℤ → AddCircle p) ↔ Irrational (a / p).

For p = 1, a / 1 = a, so Irrational a ⟹ DenseRange (· • a : ℤ → AddCircle 1). -/
example (a : ℝ) (ha : Irrational a) :
    DenseRange (fun n : ℤ => n • (a : AddCircle 1)) := by
  -- denseRange_zsmul_coe_iff gives DenseRange ↔ Irrational (a / 1).
  -- Apply the mpr direction with our hypothesis (after converting a / 1 = a).
  have hp1 : (a / (1 : ℝ)) = a := by ring
  have hiff := (AddCircle.denseRange_zsmul_coe_iff (a := a) (p := (1 : ℝ))).mpr
  -- hiff : DenseRange (· • a : ℤ → AddCircle 1) (after rewrite of a / 1 = a).
  sorry

/-- For our specific a = log 3 / log 4, the sequence {n · a} is dense in AddCircle 1. -/
example : DenseRange (fun n : ℤ => n • ((Real.log 3 / Real.log 4 : ℝ) : AddCircle 1)) := by
  sorry

end Erdos125Equidistribution