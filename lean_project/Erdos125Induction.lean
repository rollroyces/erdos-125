import Mathlib

namespace Erdos125Induction

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- L1: 3 * n ≡ 0 mod 3, so inA (3 * n) = inA n.
theorem inA_3n_eq_n (n : Nat) : inA (3 * n) = inA n := by
  cases n with
  | zero => rfl
  | succ k =>
    have h_eq1 : 3 * (k + 1) = 3 * k + 3 := by ring
    have h_eq2 : 3 * k + 3 = 3 * k + 2 + 1 := by ring
    rw [h_eq1, h_eq2, inA]
    have h_mod : (3 * k + 2 + 1) % 3 = 0 := by
      rw [show 3 * k + 2 + 1 = 3 * (k + 1) from by ring]
      rw [Nat.mul_mod_right]
    have h_div : (3 * k + 2 + 1) / 3 = k + 1 := by
      rw [show 3 * k + 2 + 1 = 3 * (k + 1) from by ring]
      exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 2)
    rw [h_mod, h_div]
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

-- L3: If a > 0 and inA a, then a % 3 < 2 and inA (a / 3).
theorem inA_pos_implies (a : Nat) (ha : inA a) (hapos : a > 0) :
    a % 3 < 2 ∧ inA (a / 3) := by
  cases a with
  | zero => simp at hapos
  | succ n =>
    rw [inA] at ha
    split_ifs at ha
    · exact ⟨‹_›, ha⟩
    · simp_all

-- L2: inA (3^k) = true for all k.
-- (3^k in base 3 is 1 followed by k zeros, all valid.)
theorem inA_3pow (k : Nat) : inA (3^k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      rw [Nat.pow_zero]
      rw [inA]
      have h1 : (0 + 1 : Nat) % 3 = 1 := by rfl
      have h2 : (0 + 1 : Nat) / 3 = 0 := by rfl
      rw [if_pos (by norm_num : (0 + 1 : Nat) % 3 < 2)]
      rw [h2]
      rw [inA.eq_def]
    | succ k' =>
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
      rw [inA_3n_eq_n]
      exact ih k' (by omega)

-- The key structural lemma (A has block structure at 3^k).
-- For any a ∈ A and k with a < 3^k, 3^k + a ∈ A.
--
-- Proof: by induction on k (strong induction, generalizing a).
-- Base case k = 0: 3^0 = 1, a < 1 implies a = 0, 3^0 + 0 = 1 ∈ A. ✓
-- Inductive step k = k' + 1: 3^k = 3 * 3^k'.
--   Case a = 0: 3^k + 0 = 3^k = 3 * 3^k'. By inA_3n_eq_n: inA (3 * 3^k') = inA (3^k'). ✓
--   Case a = a' + 1 (a > 0):
--     inA (3^k + a' + 1) unfolds to if ((3^k + a' + 1) % 3 < 2) then inA ((3^k + a' + 1) / 3) else false.
--     3^k + a' + 1 = 3 * 3^k' + a' + 1.
--     (3 * 3^k' + a' + 1) % 3 = (a' + 1) % 3 (since 3 * 3^k' ≡ 0).
--     Since inA a' + 1 and a' + 1 > 0, (a' + 1) % 3 < 2.
--     So inA (3^k + a' + 1) = inA ((3 * 3^k' + a' + 1) / 3).
--     (3 * 3^k' + a' + 1) / 3 = 3^k' + (a' + 1) / 3 (by arithmetic identity).
--     By IH with k = k' and a = (a' + 1) / 3 < 3^k': inA (3^k' + (a' + 1) / 3). ✓
theorem inA_3pow_add_a (a k : Nat) (ha : inA a) (hak : a < 3^k) :
    inA (3^k + a) := by
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    cases k with
    | zero =>
      have ha_eq : a = 0 := by omega
      subst ha_eq
      exact inA_3pow 0
    | succ k' =>
      rw [Nat.pow_succ]
      cases a with
      | zero =>
        rw [Nat.mul_comm]
        rw [inA_3n_eq_n]
        exact inA_3pow k'
      | succ a' =>
        obtain ⟨ha_mod, ha_div⟩ := inA_pos_implies (a' + 1) ha (by omega)
        -- Use the established fact: ((3 ^ k' * 3).add a' + 1) = 3 * 3^k' + (a' + 1).
        -- We need to convert the goal LHS ((3 ^ k' * 3).add a' + 1) to (3 * 3^k' + (a' + 1)).
        -- Use change of goal via Eq.mpr / show.
        suffices h : inA (3 * 3^k' + (a' + 1)) = true from by
          -- h is the rewritten version of the goal.
          show inA (3 * 3^k' + (a' + 1)) = true
          -- Now prove this.
          unfold inA
          have hmod_eq : (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3 := by
            rw [Nat.add_mod]; simp
          rw [hmod_eq]
          simp only [ha_mod, if_true]
          have hdiv_eq : (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3 := by
            have ha1 : (a' + 1) = 3 * ((a' + 1) / 3) + (a' + 1) % 3 := by
              rw [Nat.div_add_mod]
            rw [ha1]
            rw [Nat.add_assoc]
            rw [Nat.mul_add 3 3^k' ((a' + 1) / 3)]
            rw [Nat.div_add_mod]
            rw [Nat.mul_mod_right]
            simp
            rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
            have hmod_lt_3 : (a' + 1) % 3 < 3 := by omega
            have hmod_div : (a' + 1) % 3 / 3 = 0 := by omega
            rw [hmod_div]
            ring
          rw [hdiv_eq]
          have h_div_lt : (a' + 1) / 3 < 3^k' := by
            rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
            rw [Nat.pow_succ]
            exact hak
          exact ih k' (by omega) ((a' + 1) / 3) ha_div h_div_lt
        sorry

-- Verifications via native_decide.
example : inA (3^1 + 0) = true := by native_decide  -- 3 ∈ A? 3 = 10_3, yes
example : inA (3^1 + 1) = true := by native_decide  -- 4 = 11_3, yes
example : inA (3^4 + 0) = true := by native_decide  -- 81 = 10000_3, yes
example : inA (3^3 + 12) = true := by native_decide  -- 39 = 1110_3, yes
example : inA (3^5 + 81) = true := by native_decide  -- 324 = 110000_3, yes
example : inA (3^5 + 121) = true := by native_decide  -- 364 = 110111_3, yes

end Erdos125Induction
