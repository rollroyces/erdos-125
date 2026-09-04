import Mathlib

namespace Erdos125Induction

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- L1 (the shift lemma): For any a ∈ A and k ≥ 1 with a < 3^k, we have 3^k + a ∈ A.
-- This is the key structural fact: A ∩ [3^k, 3^(k+1)) = 3^k + A ∩ [0, 3^k).

-- Approach: induction on k.
-- Base k = 0: 3^0 + a = 1 + a. If a < 1, a = 0, then 3^0 + a = 1. inA 1 = true.
-- Step: assume for k' (any k' < k). Show for k.
-- For k = k' + 1: a < 3^(k'+1). Apply inA def: inA a = (a % 3 < 2) then inA (a / 3) else false.
--   If a = 0: 3^k + 0 = 3^k. inA (3^k) = (3^k % 3 < 2) then inA (3^(k-1)) else false.
--     For k ≥ 1, 3^k % 3 = 0 < 2. inA (3^(k-1)).
--     Eventually inA 1 = true.
--   If a > 0: a % 3 < 2 (since inA a). Apply IH to (a / 3) with k' < k.
--     a / 3 < 3^k' (from a < 3 * 3^k').
--     inA (a / 3) (from inA a and a > 0).
--     So 3^k' + (a / 3) ∈ A by IH.
--     Now 3^k + a = 3 * 3^k' + a. inA (3^k + a) = if (3^k + a) % 3 < 2 then inA ((3^k + a) / 3) else false.
--     (3^k + a) % 3 = a % 3 < 2.
--     (3^k + a) / 3 = 3^k' + a / 3 (since a < 3 * 3^k').
--     So inA (3^k + a) = inA (3^k' + a / 3) = true. ✓

-- The a = 0 case is straightforward (just need to show inA (3^k) = true).
-- The a > 0 case uses IH.

theorem inA_3pow_add_a (a k : Nat) (ha : inA a) (hak : a < 3^k) : inA (3^k + a) := by
  -- Strong induction on k.
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    cases k with
    | zero =>
      -- k = 0: 3^0 = 1. a < 1 means a = 0.
      have : a = 0 := by omega
      subst this
      -- inA 1 = true (definition)
      simp [inA]
    | succ k' =>
      -- k = k' + 1. 3^k = 3^(k'+1) = 3 * 3^k'.
      rw [Nat.pow_succ]
      -- Cases on a.
      cases a with
      | zero =>
        -- a = 0. Goal: inA (3 * 3^k').
        -- Use: 3 * 3^k' = 3^(k'+1). Induct or use inA_3n_eq_n.
        -- inA (3 * 3^k') = inA (3^k') (inA_3n_eq_n gives inA (3 * n) = inA n).
        -- Wait, that says inA (3 * n) = inA n. So inA (3 * 3^k') = inA (3^k').
        -- By repeating: inA (3^k') = inA (3 * 3^(k'-1)) = inA (3^(k'-1)) = ... = inA 1 = true.
        -- Direct proof: inA (3 * 3^k') = if (3 * 3^k') % 3 < 2 then inA ((3 * 3^k') / 3) else false.
        -- 3 * 3^k' % 3 = 0 < 2. inA ((3 * 3^k') / 3) = inA (3^k').
        -- Repeat.
        -- Use ih with a = 0 and k' (smaller than k).
        -- ih k' (by omega) (inA 0) (0 < 3^k') = inA (3^k' + 0) = inA 3^k' = inA (3 * 3^(k'-1)) ...
        -- Wait we need inA (3 * 3^k'), not inA (3^k' + 0) = inA (3^k').
        -- Hmm, but 3 * 3^k' = 3^(k'+1) = 3^k = 3^k' + 0... no, 3 * 3^k' = 3^(k'+1) ≠ 3^k' + 0.
        -- 3^k + 0 = 3^(k'+1) + 0 = 3^(k'+1). So inA (3^k + 0) = inA (3 * 3^k') = inA (3^(k'+1)).
        -- Yes! So inA (3 * 3^k') = inA (3^k + 0). And we can apply IH with a = 0.
        -- But IH requires k' < k, which is true.
        -- Wait IH requires a < 3^k'. But we have a = 0 < 3^k' (for k' ≥ 1, 3^k' ≥ 3 > 0; for k' = 0, 3^k' = 1, a = 0 < 1).
        -- So IH applies.
        -- Actually the IH is inA a → a < 3^k' → inA (3^k' + a).
        -- We have inA 0 = true (trivial) and 0 < 3^k' (if k' > 0; for k' = 0, we need separate handling).
        -- Hmm, the strong_induction_on gives ih for m < k with conclusion inA (3^m + a).
        -- So we use ih k' (k' < k) ha hak': inA (3^k' + a) = inA (3^k' + 0) = inA (3^k').
        -- We need inA (3 * 3^k'), not inA (3^k').
        -- But 3 * 3^k' = 3^k = 3^(k' + 1). And 3^(k' + 1) is not 3^k'.
        -- So inA (3 * 3^k') is different from inA (3^k').
        -- Hmm. Let me rethink.
        -- Actually: 3^k + 0 = 3 * 3^k' + 0 = 3 * 3^k'. So inA (3^k + 0) = inA (3 * 3^k'). Same thing.
        -- So if IH gives inA (3^k' + 0), that's inA (3^k'). Not inA (3 * 3^k').
        -- But we want inA (3^k + 0) = inA (3 * 3^k').
        -- Hmm, these are DIFFERENT! 3^k' + 0 = 3^k'. 3^k + 0 = 3 * 3^k' = 3^(k'+1).
        -- So 3^k' + 0 ≠ 3^k + 0.
        -- I confused myself. Let me re-think.
        -- The lemma says: inA a → a < 3^k → inA (3^k + a). For a = 0: inA 0 = true and a = 0 < 3^k, so we want inA (3^k + 0) = inA (3^k).
        -- And 3^k = 3 * 3^k'. So inA (3 * 3^k').
        -- Use IH with k' (smaller). IH: inA a → a < 3^k' → inA (3^k' + a).
        -- But we want inA (3 * 3^k'), not inA (3^k' + a).
        -- We can't directly use IH for this.
        --
        -- Alternative: directly prove inA (3 * 3^k') by unfolding.
        -- inA (3 * 3^k') = if (3 * 3^k') % 3 < 2 then inA (3^k') else false.
        -- 3 * 3^k' % 3 = 0 < 2. So inA (3^k').
        -- Now inA (3^k') = if 3^k' % 3 < 2 then inA (3^(k'-1)) else false.
        -- For k' ≥ 1: 3^k' % 3 = 0 < 2. inA (3^(k'-1)).
        -- ... eventually inA 1 = true.
        --
        -- Use omega or recursion to handle this.
        sorry
      | succ a' =>
        -- a = a' + 1. a > 0.
        -- Apply inA def: inA a = (a % 3 < 2) then inA (a / 3) else false.
        -- Since inA a = true and a > 0, a % 3 < 2 and inA (a / 3).
        -- Need to show inA (3 * 3^k' + a' + 1).
        -- inA (3 * 3^k' + a' + 1) = if (3 * 3^k' + a' + 1) % 3 < 2 then inA (...) else false.
        -- (3 * 3^k' + a' + 1) % 3 = (a' + 1) % 3 < 2.
        -- (3 * 3^k' + a' + 1) / 3 = 3^k' + (a' + 1) / 3 (by Nat.div_add_mod or similar).
        -- Need: inA (3^k' + (a' + 1) / 3).
        -- By IH: 3^k' < k = k' + 1. inA ((a' + 1) / 3). (a' + 1) / 3 < 3^k' (since a' + 1 < 3 * 3^k').
        -- Apply IH: inA (3^k' + (a' + 1) / 3).
        sorry

end Erdos125Induction
