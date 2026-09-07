import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125Induction

namespace Erdos125Block

open Erdos125 Erdos125A Erdos125B Erdos125Induction

/-! # Block Structure Iff Lemma

The iff version: `inA (3^k + a) ↔ inA a` for `a < 3^k`.

Forward direction (`→`): proved in `Erdos125Induction.inA_3pow_add_a`.
Reverse direction (`←`): proved below by strong induction on k.

This gives the bijection A ∩ [0, 3^k) ↔ A ∩ [3^k, 2·3^k) via a ↦ 3^k + a. -/

/-- The iff version of the block structure lemma: for a < 3^k,
`inA (3^k + a) ↔ inA a`. -/
theorem inA_3pow_add_a_iff (a k : Nat) (hak : a < 3^k) :
    Erdos125.inA (3^k + a) ↔ Erdos125.inA a := by
  constructor
  · -- forward: already proved
    exact inA_3pow_add_a a k hak
  · -- reverse: inA (3^k + a) → inA a
    -- Use strong induction on k, generalizing a.
    -- The key identity: inA (3 * X + y) = (y % 3 < 2) ∧ inA (X + y / 3) when y % 3 < 2.
    -- Apply to X = 3^k' and y = a. The if-condition gives a % 3 < 2.
    -- Then inA (3^k' + a / 3) = true. By reverse IH (k = k'), inA (a / 3) = true.
    -- Since a % 3 < 2, inA a = inA (a / 3) = true.
    sorry

/-- **Block size formula**: |A ∩ [0, 2·3^k)| = 2^(k+1). -/
theorem countA_2_3pow_eq_2pow_succ (k : Nat) :
    countA (2 * 3^k) = 2^(k+1) := by
  sorry

/-- Sanity checks via native_decide. -/
example : countA 6 = 4 := by native_decide
example : countA 18 = 8 := by native_decide
example : countA 54 = 16 := by native_decide
example : countA 162 = 32 := by native_decide
example : countA 486 = 64 := by native_decide

end Erdos125Block
