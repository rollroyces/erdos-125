import Mathlib

namespace Erdos125Induction

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- L1: 3 * n ≡ 0 mod 3, so inA (3 * n) = inA n.
theorem inA_3n_eq_n (n : Nat) : inA (3 * n) = inA n := by
  rw [inA]
  rw [show (3 * n) % 3 = 0 from by rw [Nat.mul_mod_right]]
  simp

-- L2: inA (3^k) is always true (3^k in base 3 is 1 followed by k zeros).
theorem inA_3pow (k : Nat) : inA (3^k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp [Nat.pow_zero, inA]
    | succ k' =>
      rw [Nat.pow_succ]
      rw [inA_3n_eq_n]
      exact ih k' (by omega)

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

-- Main structural lemma: A has block structure at 3^k.
-- For any a ∈ A with a < 3^k, 3^k + a ∈ A.
-- (Equivalent: A ∩ [3^k, 3^(k+1)) = 3^k + A ∩ [0, 3^k).)
theorem inA_3pow_add_a (a k : Nat) (ha : inA a) (hak : a < 3^k) :
    inA (3^k + a) := by
  -- Strong induction on k, generalizing a.
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    cases k with
    | zero =>
      -- 3^0 = 1. a < 1 means a = 0.
      have ha_eq : a = 0 := by omega
      subst ha_eq
      exact inA_3pow 0
    | succ k' =>
      rw [Nat.pow_succ]
      cases a with
      | zero =>
        rw [inA_3n_eq_n]
        exact inA_3pow k'
      | succ a' =>
        obtain ⟨ha_mod, ha_div⟩ := inA_pos_implies (a' + 1) ha (by omega)
        -- We want: inA (3 * 3^k' + (a' + 1)).
        -- Unfold inA:
        unfold inA
        -- Mod: (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3.
        -- Use simp to evaluate mod.
        have hmod_eq : (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3 := by
          rw [Nat.add_mod]; simp
        -- Convert ((3 ^ k' * 3).add a' + 1) to (3 * 3^k' + (a' + 1)) using ac_rfl.
        -- ac_rfl handles associativity/commutativity.
        have heq : ((3 ^ k' * 3).add a' + 1) = 3 * 3^k' + (a' + 1) := by ac_rfl
        rw [heq]
        rw [hmod_eq]
        simp only [ha_mod, if_true]
        -- Need: inA ((3 * 3^k' + (a' + 1)) / 3) = inA (3^k' + (a' + 1) / 3).
        have hdiv_eq : (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3 := by
          have h : (a' + 1) = 3 * ((a' + 1) / 3) + (a' + 1) % 3 := by
            rw [Nat.div_add_mod]
          rw [h]
          -- Now: (3 * 3^k' + 3 * ((a' + 1) / 3) + (a' + 1) % 3) / 3.
          rw [Nat.add_assoc]
          rw [Nat.mul_add 3 ((a' + 1) / 3) ((a' + 1) % 3)]
          rw [Nat.mul_add 3 3^k' ((a' + 1) / 3)]
          -- Now: 3 * (3^k' + (a' + 1) / 3) + (a' + 1) % 3.
          rw [Nat.div_add_mod]
          rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
          -- Now goal: 3^k' + (a' + 1) / 3 + ((a' + 1) % 3) / 3 = 3^k' + (a' + 1) / 3.
          have hmod_lt_3 : (a' + 1) % 3 < 3 := by omega
          have hmod_div : (a' + 1) % 3 / 3 = 0 := by omega
          rw [hmod_div]
          ring
        rw [hdiv_eq]
        -- Apply IH with all 4 arguments.
        exact ih k' (by omega) ((a' + 1) / 3) ha_div (by omega)

-- Verifications: the lemma is TRUE at specific (a, k).
-- All values here are chosen so that a ∈ A and a < 3^k.
example : inA (3^1 + 0) = true := by native_decide
example : inA (3^1 + 1) = true := by native_decide
example : inA (3^4 + 0) = true := by native_decide
example : inA (3^3 + 12) = true := by native_decide
example : inA (3^5 + 81) = true := by native_decide
example : inA (3^5 + 121) = true := by native_decide

end Erdos125Induction
