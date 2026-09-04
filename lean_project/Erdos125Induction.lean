import Mathlib

namespace Erdos125Induction

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- L1: 3 * n ≡ 0 mod 3, so inA (3 * n) = inA n.
theorem inA_3n_eq_n : ∀ n, inA (3 * n) = inA n := by
  intro n
  rw [inA]
  have h : (3 * n) % 3 = 0 := by rw [Nat.mul_mod_right]
  rw [h]
  simp

-- L2: If a > 0 and inA a, then a % 3 < 2 and inA (a / 3).
theorem inA_pos_implies (a : Nat) (ha : inA a) (hapos : a > 0) :
    a % 3 < 2 ∧ inA (a / 3) := by
  obtain ⟨n, hn⟩ : ∃ n, a = n + 1 := by
    cases a with
    | zero => simp at hapos
    | succ n => exact ⟨n, rfl⟩
  subst hn
  rw [inA] at ha
  split_ifs at ha
  · exact ⟨‹_›, ha⟩
  · simp_all

-- Block structure of A at 3^k.
-- This is the key structural lemma needed to prove Case 2 by induction on density.
--
-- We state the lemma and provide native_decide verifications for several values.
-- The full general proof would follow the same structure as the existing proofs in
-- Erdos125.lean (inA_3n_eq_n) but with deeper arithmetic handling.
theorem inA_3pow_add_a (a k : Nat) (ha : inA a) (hak : a < 3^k) :
    inA (3^k + a) := by
  -- Induction on k. (Strong induction, generalizing a.)
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    -- Cases on k.
    cases k with
    | zero =>
      -- k = 0: 3^0 = 1. a < 1 means a = 0.
      have ha_eq : a = 0 := by omega
      subst ha_eq
      -- Show inA 1 = true.
      rw [inA]; simp
    | succ k' =>
      -- k = k' + 1. 3^k = 3 * 3^k'.
      rw [Nat.pow_succ]
      -- Cases on a.
      cases a with
      | zero =>
        -- a = 0. Goal: inA (3 * 3^k') = inA (3^k').
        -- By inA_3n_eq_n.
        rw [inA_3n_eq_n]
        -- Apply IH: inA (3^k' + 0) = inA (3^k'). Need to show 0 < 3^k'.
        exact ih k' (by omega) (inA_3pow_helper k') (by simp)
      | succ a' =>
        -- a = a' + 1. Use inA def.
        obtain ⟨ha_mod, ha_div⟩ := inA_pos_implies (a' + 1) ha (by omega)
        -- Goal: inA (3 * 3^k' + a' + 1).
        -- By unfolding inA:
        --   inA (n+1) = if (n+1) % 3 < 2 then inA ((n+1) / 3) else false
        -- So inA (3 * 3^k' + a' + 1) = if (3 * 3^k' + a' + 1) % 3 < 2 then inA ((3 * 3^k' + a' + 1) / 3) else false
        -- We have (3 * 3^k' + a' + 1) % 3 = (a' + 1) % 3 (since 3 * 3^k' ≡ 0 mod 3)
        -- And (a' + 1) % 3 < 2 (from ha_mod).
        -- So inA (3 * 3^k' + a' + 1) = inA ((3 * 3^k' + a' + 1) / 3)
        -- We need to show (3 * 3^k' + a' + 1) / 3 = 3^k' + (a' + 1) / 3
        -- Then inA (3^k' + (a' + 1) / 3) by IH.
        --
        -- The arithmetic regrouping is the hard part. We use a TACTIC combination:
        unfold inA
        -- First handle the if-condition: (3 * 3^k' + a' + 1) % 3 < 2.
        have hmod_eq : (3 * 3^k' + a' + 1) % 3 = (a' + 1) % 3 := by
          rw [Nat.add_mod]; simp
        rw [hmod_eq]
        simp only [ha_mod]
        -- Now: inA ((3 * 3^k' + a' + 1) / 3)
        -- Prove (3 * 3^k' + a' + 1) / 3 = 3^k' + (a' + 1) / 3.
        -- Key: a' + 1 = 3 * ((a' + 1) / 3) + (a' + 1) % 3.
        -- (a' + 1) % 3 < 3, so (a' + 1) % 3 / 3 = 0.
        -- Hence 3 * 3^k' + a' + 1 = 3 * (3^k' + (a' + 1) / 3) + (a' + 1) % 3.
        -- Divide by 3: 3^k' + (a' + 1) / 3.
        have hdiv_eq : (3 * 3^k' + a' + 1) / 3 = 3^k' + (a' + 1) / 3 := by
          rw [Nat.div_add_mod]
          rw [Nat.mul_mod_right]; simp
          rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
          -- Now goal: (a' + 1) / 3 + 3^k' + (a' + 1) % 3 / 3 = 3^k' + (a' + 1) / 3
          -- (a' + 1) % 3 / 3 = 0 since (a' + 1) % 3 < 3.
          have hmod_div : (a' + 1) % 3 / 3 = 0 := by
            have h : (a' + 1) % 3 < 3 := by omega
            omega
          rw [hmod_div]
          ring
        rw [hdiv_eq]
        -- Apply IH: inA (3^k' + (a' + 1) / 3).
        have h_div_lt : (a' + 1) / 3 < 3^k' := by
          rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
          exact hak
        exact ih k' (by omega) ha_div h_div_lt

-- Helper lemma: inA (3^k) is true for all k.
-- This is needed for the a = 0 case.
theorem inA_3pow_helper (k : Nat) : inA (3^k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [Nat.pow_zero, inA]
    | succ k' =>
      rw [Nat.pow_succ]
      rw [inA_3n_eq_n]
      exact ih k' (by omega)

-- Verifications via native_decide: confirms the lemma at specific (a, k).
-- All these should be TRUE if inA_3pow_add_a is correct.
example : inA (3^1 + 0) = true := by native_decide  -- 3, in A? 3 = 10_3, yes
example : inA (3^1 + 1) = true := by native_decide  -- 4, in A? 4 = 11_3, yes
example : inA (3^4 + 0) = true := by native_decide  -- 81, in A? 81 = 10000_3, yes
example : inA (3^3 + 12) = true := by native_decide  -- 39, in A? 39 = 1110_3, yes
example : inA (3^5 + 81) = true := by native_decide  -- 324, in A? 81 = 10000_3, 324 = 81*4 = 324 = 81 + 243, 81+243=324, in base 3 = 110000. All 0/1, yes
example : inA (3^5 + 121) = true := by native_decide  -- 364, in A? 121 = 11111_3, 364 = 121 + 243 = 364 = 110111_3, all 0/1, yes

end Erdos125Induction
