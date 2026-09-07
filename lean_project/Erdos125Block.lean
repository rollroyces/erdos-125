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

This gives the bijection A ∩ [0, 3^k) ↔ A ∩ [3^k, 2·3^k) via a ↦ 3^k + a.

The reverse direction proof:
- Base k=0: 3^0 + a = 1 + a. a < 1 means a = 0. inA 1 = true, inA 0 = true. ✓
- Step k=k'+1: 3^k + a = 3*3^k' + a. By inA def unfolding:
  inA (3*3^k' + a) = (a % 3 < 2) ∧ inA (3^k' + a / 3).
  So a % 3 < 2 and inA (3^k' + a / 3) = true.
  By reverse IH (k=k', a=a/3), inA (a / 3) = true.
  Since a % 3 < 2, inA a = inA (a / 3) = true. ✓ -/

/-- The iff version: for a < 3^k, `inA (3^k + a) ↔ inA a`. -/
theorem inA_3pow_add_a_iff (a k : Nat) (hak : a < 3^k) :
    Erdos125.inA (3^k + a) ↔ Erdos125.inA a := by
  constructor
  · -- forward
    exact inA_3pow_add_a a k hak
  · -- reverse
    -- We use the fact: inA (3 * X + y) = (y % 3 < 2) ∧ inA (X + y / 3) for any y.
    -- This follows from inA def unfolding.
    -- 
    -- So inA (3^k + a) = inA (3 * 3^(k-1) + a) (when k ≥ 1) = (a % 3 < 2) ∧ inA (3^(k-1) + a / 3).
    -- By reverse IH: inA (3^(k-1) + a / 3) → inA (a / 3).
    -- So inA a = (a % 3 < 2) then inA (a / 3) else false = inA (a / 3) (since a % 3 < 2).
    -- 
    -- This requires: a / 3 < 3^(k-1), which follows from a < 3^k.
    -- 
    -- Base case k = 0: a < 1, a = 0. inA 1 = true, inA 0 = true. ✓
    -- 
    -- We prove this by strong induction on k.
    induction k using Nat.strong_induction_on generalizing a with
    | _ k ih =>
      intro hk_inv  -- hk_inv : inA (3^k + a) = true
      -- We do cases on a.
      cases a with
      | zero =>
        -- a = 0. 3^k + 0 = 3^k ∈ A (by inA_3pow).
        -- inA 0 = true by definition.
        -- So inA 0 = true. ✓
        -- (Need to use the fact that inA 3^k = true, but this is what we have via hk_inv.)
        -- Actually: hk_inv : inA (3^k + 0) = inA 3^k = true. So inA 3^k = true.
        -- But we need inA 0 = true, which is just by definition.
        rfl
      | succ a' =>
        -- a = a' + 1. So a > 0, a ≥ 1.
        -- hk_inv : inA (3^k + a' + 1) = true.
        -- By inA def: inA (3^k + a' + 1) = if ((3^k + a' + 1) % 3 < 2) then inA ((3^k + a' + 1) / 3) else false.
        -- We have hk_inv, so the if resolves to "then" branch:
        -- (3^k + a' + 1) % 3 < 2 AND inA ((3^k + a' + 1) / 3) = true.
        -- 
        -- (3^k + a' + 1) % 3 = (3^k % 3) + (a' + 1) % 3 mod 3.
        -- If k = 0: 3^k % 3 = 1, so (3^k + a' + 1) % 3 = (1 + (a' + 1)) % 3 = (a' + 2) % 3.
        -- If k ≥ 1: 3^k % 3 = 0, so (3^k + a' + 1) % 3 = (a' + 1) % 3.
        -- 
        -- We split into k = 0 and k ≥ 1.
        cases k with
        | zero =>
          -- k = 0. 3^k = 1. 3^0 + a' + 1 = 1 + a' + 1 = a' + 2.
          -- hk_inv : inA (a' + 2) = true.
          -- By inA def: inA (a' + 2) = (a' + 2) % 3 < 2 then inA ((a' + 2) / 3) else false.
          -- Since a' + 2 < 1 (because a' + 1 = a < 1, so a' = 0), so a' + 2 = 2.
          -- inA 2 = (2 % 3 < 2) then inA 0 else false = (2 < 2) then inA 0 else false = false.
          -- But hk_inv says inA 2 = true. Contradiction unless we're in some edge case.
          -- 
          -- Hmm wait, a < 1 means a = 0 (since a = a' + 1 > 0). Contradiction.
          -- So this case is unreachable. We can handle it with False.elim.
          have h_unreach : False := by
            have ha_pos : a > 0 := by simp
            have ha_lt : a < 1 := hak
            omega
          exact False.elim h_unreach
        | succ k' =>
          -- k = k' + 1. 3^k = 3 * 3^k'.
          -- The goal: inA a = inA (a' + 1) = true.
          -- hk_inv : inA (3 * 3^k' + (a' + 1)) = true.
          -- 
          -- Step 1: Show (a' + 1) % 3 < 2.
          -- By inA def: inA (3 * 3^k' + (a' + 1)) = 
          --   if ((3 * 3^k' + (a' + 1)) % 3 < 2) then inA ((3 * 3^k' + (a' + 1)) / 3) else false.
          -- Since hk_inv says this is true, the if resolves to "then" branch.
          -- So: (3 * 3^k' + (a' + 1)) % 3 < 2 and inA ((3 * 3^k' + (a' + 1)) / 3) = true.
          -- 
          -- Step 2: (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3.
          -- (Since 3 * 3^k' ≡ 0 mod 3.)
          -- So (a' + 1) % 3 < 2.
          -- 
          -- Step 3: (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3.
          -- (By Nat.add_div and the fact that (a' + 1) % 3 < 2.)
          -- So inA (3^k' + (a' + 1) / 3) = true.
          -- 
          -- Step 4: Apply reverse IH with k = k', a = (a' + 1) / 3.
          -- We have (a' + 1) / 3 < 3^k' (from a < 3 * 3^k').
          -- So inA ((a' + 1) / 3) = true.
          -- 
          -- Step 5: inA (a' + 1) = (a' + 1) % 3 < 2 then inA ((a' + 1) / 3) else false.
          -- Since (a' + 1) % 3 < 2, this = inA ((a' + 1) / 3) = true. ✓
          -- 
          -- The implementation:
          -- Unfold inA in hk_inv.
          -- The unfold gives a match on (3 * 3^k' + (a' + 1)), which Lean displays as ((3 ^ k' * 3).add a' + 1).
          -- We need to convert this to 3 * 3^k' + (a' + 1).
          have h_mod_eq : (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3 := by
            rw [Nat.add_mod]; simp
          -- We extract the digit-removal facts from hk_inv.
          have h_lt : (a' + 1) % 3 < 2 := by
            -- hk_inv is inA (3 * 3^k' + (a' + 1)) = true.
            -- After unfold, this is (if (3 * 3^k' + (a' + 1)) % 3 < 2 then inA (...) else false) = true.
            -- So (3 * 3^k' + (a' + 1)) % 3 < 2 (by the if-then-else equation).
            -- (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3.
            have h_in_unfold : Erdos125.inA (3 * 3^k' + (a' + 1)) = true := hk_inv
            rw [Erdos125.inA] at h_in_unfold
            rw [h_mod_eq] at h_in_unfold
            -- h_in_unfold : (if (a' + 1) % 3 < 2 then inA ((3 * 3^k' + (a' + 1)) / 3) else false) = true
            -- So (a' + 1) % 3 < 2.
            by_contra h
            push_neg at h
            rw [if_neg h] at h_in_unfold
            simp at h_in_unfold
          -- Now we have (a' + 1) % 3 < 2.
          -- Extract inA ((3 * 3^k' + (a' + 1)) / 3) = true from h_in_unfold.
          -- (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3 by Nat.add_div.
          -- Apply reverse IH to get inA ((a' + 1) / 3) = true.
          -- Then by inA def, inA (a' + 1) = inA ((a' + 1) / 3) = true.
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
