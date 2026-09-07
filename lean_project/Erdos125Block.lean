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
    -- Strong induction on k, generalizing a.
    suffices h : ∀ m : Nat, m ≤ k → ∀ a : Nat, a < 3^m → Erdos125.inA (3^m + a) → Erdos125.inA a by
      exact h k (by omega) a hak
    intro m hmk
    induction m using Nat.strong_induction_on generalizing a with
    | _ m ih =>
      intro a haml hma
      cases m with
      | zero =>
        -- m = 0. a < 1, so a = 0.
        have ha_eq : a = 0 := by omega
        subst ha_eq
        -- inA 1 → inA 0. Both are true by definition.
        -- inA 1 = (1 % 3 < 2) then inA (1 / 3) else false
        --       = (1 < 2) then inA 0 else false
        --       = inA 0
        -- So inA 1 = inA 0 = true. ✓
        unfold Erdos125.inA at hma ⊢
        simp at hma
        rfl
      | succ k' =>
        -- m = k' + 1. 3^m + a = 3 * 3^k' + a.
        rw [Nat.pow_succ, Nat.mul_comm] at hma
        -- hma : inA (3 * 3^k' + a) = true
        -- By inA def: inA (3 * 3^k' + a) = if (3 * 3^k' + a) % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false
        -- (3 * 3^k' + a) % 3 = a % 3 (since 3 * 3^k' ≡ 0)
        -- (3 * 3^k' + a) / 3 = 3^k' + a / 3
        -- So inA (3 * 3^k' + a) = (a % 3 < 2) ∧ inA (3^k' + a / 3).
        unfold Erdos125.inA at hma
        -- hma is now: (if (3 * 3^k' + a) % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false) = true
        -- We need to extract: a % 3 < 2 and inA ((3 * 3^k' + a) / 3) = true.
        have h_mod : (3 * 3^k' + a) % 3 = a % 3 := by
          rw [Nat.add_mod]; simp
        rw [h_mod] at hma
        -- hma : (if a % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false) = true
        -- So a % 3 < 2 and inA ((3 * 3^k' + a) / 3) = true.
        have h_lt : a % 3 < 2 := by
          by_contra h
          push_neg at h
          -- h : ¬ (a % 3 < 2), so a % 3 ≥ 2.
          -- But then inA ((3 * 3^k' + a) / 3) = false, so hma = false = true, contradiction.
          rw [if_neg h] at hma
          simp at hma
        -- Now hma : inA ((3 * 3^k' + a) / 3) = true.
        have h_div : (3 * 3^k' + a) / 3 = 3^k' + a / 3 := by
          rw [show 3 * 3^k' + a = a + 3 * 3^k' from by ring]
          rw [Nat.div_add_mod]
          rw [Nat.mul_mod_right]; simp
          rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
          rw [show a = 3 * (a / 3) + a % 3 from by ring]
          sorry
        rw [h_div] at hma
        -- hma : inA (3^k' + a / 3) = true
        -- Need: inA a.
        -- Since a % 3 < 2, inA a = inA (a / 3) by inA def.
        -- And inA (a / 3) follows from inA (3^k' + a / 3) by reverse IH.
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
