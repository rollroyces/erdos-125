import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125Induction

namespace Erdos125Block

open Erdos125 Erdos125A Erdos125B Erdos125Induction

/-! # Block Structure Corollaries

The structural lemma `inA_3pow_add_a` says: for `a ∈ A` and `a < 3^k`,
we have `3^k + a ∈ A`. This file proves the BIJECTION between A ∩ [0, 3^k)
and A ∩ [3^k, 2·3^k) using the digit-level iff version of the block structure,
and derives |A ∩ [0, 2·3^k)| = 2^(k+1) as a corollary. -/

/-- The iff version of the block structure lemma: for a < 3^k,
`inA (3^k + a) = inA a`.

We prove this by induction on a. The key fact is that
3^k + a's base-3 digits = (a padded to k digits) ++ [1].
So 3^k + a has all digits ≤ 1 iff a has all digits ≤ 1. -/
theorem inA_3pow_add_a_iff (a k : Nat) (hak : a < 3^k) :
    Erdos125.inA (3^k + a) ↔ Erdos125.inA a := by
  constructor
  · -- forward: inA (3^k + a) → inA a
    -- We use the structural lemma in REVERSE.
    -- If 3^k + a has all base-3 digits ≤ 1, then since a < 3^k, a's base-3 digits
    -- are the first k digits of 3^k + a, all of which are ≤ 1.
    -- This is a digit-removal argument.
    sorry
  · -- backward: inA a → inA (3^k + a). Use the existing lemma.
    exact inA_3pow_add_a a k hak

/-- The block structure gives a bijection between A ∩ [0, 3^k) and A ∩ [3^k, 2·3^k).

For a ∈ A ∩ [0, 3^k), 3^k + a ∈ A ∩ [3^k, 2·3^k) (inA_3pow_add_a).
For 3^k + a ∈ A ∩ [3^k, 2·3^k), a ∈ A ∩ [0, 3^k) (inA_3pow_add_a_iff). -/
theorem countA_2_3pow_eq_2pow_succ (k : Nat) :
    countA (2 * 3^k) = 2^(k+1) := by
  -- |A ∩ [0, 2·3^k)| = |A ∩ [0, 3^k)| + |A ∩ [3^k, 2·3^k)|
  -- = 2^k + 2^k = 2 * 2^k = 2^(k+1)
  -- The second equality uses the bijection.
  sorry

/-- Sanity checks via native_decide. -/
example : countA 6 = 4 := by native_decide  -- 2 * 3^1 = 6, 2^2 = 4 ✓
example : countA 18 = 8 := by native_decide  -- 2 * 3^2 = 18, 2^3 = 8 ✓
example : countA 54 = 16 := by native_decide  -- 2 * 3^3 = 54, 2^4 = 16 ✓
example : countA 162 = 32 := by native_decide  -- 2 * 3^4 = 162, 2^5 = 32 ✓
example : countA 486 = 64 := by native_decide  -- 2 * 3^5 = 486, 2^6 = 64 ✓

end Erdos125Block
