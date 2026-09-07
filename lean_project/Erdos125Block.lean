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

-- Helper: m < 3 implies m / 3 = 0 (also m % 3 = m).
lemma mod_lt_self_div (m : Nat) (h : m < 3) : m / 3 = 0 := by
  omega

/-- The iff version of the block structure lemma: for a < 3^k,
`inA (3^k + a) ↔ inA a`. -/
theorem inA_3pow_add_a_iff (a k : Nat) (hak : a < 3^k) :
    Erdos125.inA (3^k + a) ↔ Erdos125.inA a := by
  constructor
  · -- forward: already proved
    exact inA_3pow_add_a a k hak
  · -- reverse: inA (3^k + a) → inA a
    -- We do strong induction on k, generalizing a.
    induction k using Nat.strong_induction_on generalizing a with
    | _ k ih =>
      intro hk_inv
      cases k with
      | zero =>
        -- 3^0 = 1, a < 1, so a = 0.
        have ha_eq : a = 0 := by omega
        subst ha_eq
        -- inA 1 = inA 0 (both true).
        -- inA 1 = (1 % 3 < 2) then inA (1/3) else false = (1 < 2) then inA 0 else false = inA 0.
        -- So inA 1 = inA 0 = true.
        -- hk_inv : inA 1 = true. Goal: inA 0 = true.
        -- We have inA 0 = true by definition. Use that.
        -- inA 0 = true. ✓
        rfl
      | succ k' =>
        -- k = k' + 1. 3^k = 3 * 3^k'.
        rw [Nat.pow_succ, Nat.mul_comm] at hk_inv
        -- hk_inv : inA (3 * 3^k' + a) = true
        -- By inA def unfolding: inA (3 * 3^k' + a) = if (3 * 3^k' + a) % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false.
        -- 3 * 3^k' % 3 = 0, so (3 * 3^k' + a) % 3 = a % 3.
        -- (3 * 3^k' + a) / 3 = 3^k' + a / 3 (by Nat.add_div).
        -- So inA (3 * 3^k' + a) = (a % 3 < 2) ∧ inA (3^k' + a / 3).
        unfold Erdos125.inA at hk_inv
        -- hk_inv is now: (if (3 * 3^k' + a) % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false) = true.
        -- By the if-true/false equation, we extract:
        -- 1. (3 * 3^k' + a) % 3 < 2
        -- 2. inA ((3 * 3^k' + a) / 3) = true
        have hmod_eq : (3 * 3^k' + a) % 3 = a % 3 := by
          rw [Nat.add_mod]; simp
        rw [hmod_eq] at hk_inv
        -- hk_inv : (if a % 3 < 2 then inA ((3 * 3^k' + a) / 3) else false) = true
        -- So a % 3 < 2 and inA ((3 * 3^k' + a) / 3) = true.
        -- First, prove a % 3 < 2.
        have h_lt : a % 3 < 2 := by
          by_contra h
          push_neg at h
          rw [if_neg h] at hk_inv
          simp at hk_inv
        -- Now hk_inv : inA ((3 * 3^k' + a) / 3) = true.
        -- Convert the division:
        have hdiv_eq : (3 * 3^k' + a) / 3 = 3^k' + a / 3 := by
          rw [show 3 * 3^k' + a = a + 3 * 3^k' from by ring]
          rw [Nat.div_add_mod]
          rw [Nat.mul_mod_right]; simp
          rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
          rw [show a = 3 * (a / 3) + a % 3 from by ring]
          rw [Nat.add_mod]; simp
          have hmod_lt : a % 3 < 3 := by omega
          have hmod_div : a % 3 / 3 = 0 := by
            apply mod_lt_self_div _ hmod_lt
          rw [hmod_div]
          ring
        rw [hdiv_eq] at hk_inv
        -- hk_inv : inA (3^k' + a / 3) = true
        -- We need: inA a.
        -- Since a % 3 < 2, inA a = inA (a / 3) (by inA def, since a > 0 OR a = 0).
        -- Need: a / 3 < 3^k' to apply IH.
        -- We have a < 3^k = 3 * 3^k', so a / 3 < 3^k' (for a > 0).
        -- Case a = 0: trivial.
        cases a with
        | zero =>
          -- a = 0. inA 0 = true.
          rfl
        | succ a' =>
          -- a = a' + 1. inA (a' + 1) = inA (a' + 1 / 3) = inA (a' / 3 + 1/3) = ...
          -- Hmm. We have a > 0, so a = a' + 1, and a / 3 = (a' + 1) / 3.
          -- (a' + 1) % 3 = a % 3 < 2, so inA (a' + 1) = inA ((a' + 1) / 3).
          -- Apply IH with k = k', a'' = (a' + 1) / 3.
          have h_div_lt : (a' + 1) / 3 < 3^k' := by
            rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
            exact hak
          have h_inv : Erdos125.inA (3^k' + (a' + 1) / 3) → Erdos125.inA ((a' + 1) / 3) := ih k' (by omega) ((a' + 1) / 3) h_div_lt
          have : Erdos125.inA (3^k' + (a' + 1) / 3) := hk_inv
          have : Erdos125.inA ((a' + 1) / 3) := h_inv this
          -- Now: inA a = inA (a' + 1) = inA ((a' + 1) / 3) = true.
          have h_mod_lt : (a' + 1) % 3 < 2 := by
            -- a % 3 < 2, but we need (a' + 1) % 3 < 2.
            -- These are the same since a = a' + 1.
            -- We have h_lt : a % 3 < 2 = (a' + 1) % 3 < 2.
            exact h_lt
          -- inA (a' + 1) = if (a' + 1) % 3 < 2 then inA ((a' + 1) / 3) else false
          --             = inA ((a' + 1) / 3)
          --             = true.
          unfold Erdos125.inA
          rw [if_pos h_mod_lt]
          exact this

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
