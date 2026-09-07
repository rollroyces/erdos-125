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
        -- The goal LHS is inA (((3 ^ k' * 3).add a' + 1).
        -- This unfolds to a complex if-then-else. The arithmetic identity
        -- (3 ^ k' * 3 = 3 * 3^k') is the issue.
        -- 
        -- Alternative approach: directly prove via decision procedure.
        -- The proposition inA (3^k + a) where a ∈ A and a < 3^k is decidable.
        -- Use `decide` to dispatch.

        -- Use IH directly without unfolding the .add notation.
        -- First, note that 3^k + (a' + 1) = 3 * 3^k' + (a' + 1) (after rw [Nat.pow_succ]).
        -- We need to show inA (3 * 3^k' + (a' + 1)).
        -- By inA def, this unfolds to:
        --   if (3 * 3^k' + (a' + 1)) % 3 < 2 then inA (...) else false
        --   = if (a' + 1) % 3 < 2 then inA (3^k' + (a' + 1) / 3) else false
        --   = inA (3^k' + (a' + 1) / 3) (by ha_mod)
        -- = IH on (a' + 1) / 3 < 3^k'
        -- 
        -- But the unfolding has the .add issue. Let me use a different approach:
        -- Define a "translated" theorem with explicit + form.

        -- Simplify: just use a direct proof by changing the goal to use 3 * 3^k'.
        -- The expression ((3 ^ k' * 3).add a' + 1) is β-equivalent to (3 * 3^k' + (a' + 1)).
        -- Use the LHS of the if-else.
        -- 
        -- Define a function to extract the inner.
        -- Actually, let me try `generalize` or `wlog` or some other tactic.

        -- Or use a different induction variable: induction on a (not k).
        -- 
        -- The base case a = 0: inA 3^k = true by inA_3pow.
        -- The step a = a' + 1: inA (3^k + a' + 1).
        -- By inA def: if ((3^k + a' + 1) % 3 < 2) then inA ((3^k + a' + 1) / 3) else false.
        -- 3^k + a' + 1 = 3 * 3^k' + a' + 1.
        -- (3 * 3^k' + a' + 1) % 3 = (a' + 1) % 3 < 2 (by ha_mod).
        -- (3 * 3^k' + a' + 1) / 3 = (3 * 3^k' + a') / 3 + 1/3 = 3^k' + a' / 3 + 0 = 3^k' + a' / 3.
        -- Wait, (a' + 1) / 3 not a' / 3. Hmm.
        -- 
        -- Actually, the identity is:
        -- (3 * X + y) / 3 = X + y / 3 (always).
        -- So (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3.
        -- 
        -- By IH (with a = (a' + 1) / 3): inA (3^k' + (a' + 1) / 3).
        -- Need: inA (a' + 1) / 3 (by inA_pos_implies).
        -- Need: (a' + 1) / 3 < 3^k' (from hak).
        -- 
        -- So the proof works. Just need to formalize the unfolding.

        -- The key fact: inA (3 * X + y) = inA (X + y / 3) when y % 3 < 2.
        -- This is the digit-removal lemma.
        -- 
        -- Proof: unfold inA. The match on (3 * X + y) is non-zero.
        -- It unfolds to if ((3X + y) % 3 < 2) then inA ((3X + y) / 3) else false.
        -- (3X + y) % 3 = y % 3 (since 3X ≡ 0). So if resolves to "then" by hy.
        -- (3X + y) / 3 = X + y / 3 (by the key identity).
        -- So inA (3X + y) = inA (X + y / 3).
        -- 
        -- But the actual proof is non-trivial due to Lean's .add notation.
        -- We use the helper lemma from Erdos125Induction2.
        have heq : inA (3 * 3^k' + (a' + 1)) = inA (3^k' + (a' + 1) / 3) := by
          rw [inA.eq_def, Nat.mul_comm]
          cases h1 : 3^k' * 3 + (a' + 1) with
          | zero => simp at h1
          | succ n1 =>
            rw [show n1 + 1 = 3^k' * 3 + (a' + 1) from h1.symm]
            have hmod_eq : (3^k' * 3 + (a' + 1)) % 3 = (a' + 1) % 3 := by
              rw [Nat.add_mod]; simp; rw [Nat.mul_mod_right]
            rw [hmod_eq]
            simp only [ha_mod, if_pos (by norm_num : 0 < 2)]
            rw [Nat.mul_comm]
            rw [show (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3 from by
              rw [Nat.add_div (3 * 3^k') (a' + 1) 3 (by norm_num : 0 < 3)]
              rw [Nat.mul_mod_right]
              rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
              have hmod_lt : (a' + 1) % 3 < 3 := by omega
              have hmod_div : (a' + 1) % 3 / 3 = 0 := by omega
              simp [hmod_lt, hmod_div]]
            rfl
        -- First, convert the goal's LHS to use 3 * 3^k' instead of 3^k' * 3.
        rw [Nat.mul_comm]
        -- Now: inA (3 * 3^k' + (a' + 1)) = true.
        rw [heq]
        -- Now: inA (3^k' + (a' + 1) / 3) = true.
        -- Apply IH.
        have h_div_lt : (a' + 1) / 3 < 3^k' := by
          rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
          rw [Nat.pow_succ]
          exact hak
        exact ih k' (by omega) ((a' + 1) / 3) ha_div h_div_lt

-- Verifications via native_decide.
example : inA (3^1 + 0) = true := by native_decide  -- 3 ∈ A? 3 = 10_3, yes
example : inA (3^1 + 1) = true := by native_decide  -- 4 = 11_3, yes
example : inA (3^4 + 0) = true := by native_decide  -- 81 = 10000_3, yes
example : inA (3^3 + 12) = true := by native_decide  -- 39 = 1110_3, yes
example : inA (3^5 + 81) = true := by native_decide  -- 324 = 110000_3, yes
example : inA (3^5 + 121) = true := by native_decide  -- 364 = 110111_3, yes

end Erdos125Induction
