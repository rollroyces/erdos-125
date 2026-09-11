import Mathlib

namespace Erdos125Induction

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Helper: inA (3^k) is always true.
-- Proof: inA (3^k) = if 3^k % 3 < 2 then inA (3^(k-1)) else false.
--        3^k % 3 = 0 < 2. inA (3^(k-1)).
--        Recurse until inA 1 = (1 % 3 < 2) then inA (1 / 3) else false = (1 < 2) then inA 0 else false = true.
theorem inA_3pow (k : Nat) : inA (3^k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      -- 3^0 = 1. inA 1.
      simp [Nat.pow_zero, inA]
    | succ k' =>
      rw [Nat.pow_succ]
      -- 3^k = 3 * 3^k'.
      -- inA (3 * 3^k') = if (3 * 3^k') % 3 < 2 then inA ((3 * 3^k') / 3) else false.
      -- 3 * 3^k' % 3 = 0 < 2. inA (3^k').
      -- Apply IH with k' < k.
      exact ih k' (by omega)

-- L1: 3 * n ≡ 0 mod 3, so inA (3 * n) = inA n.
theorem inA_3n_eq_n : ∀ n, inA (3 * n) = inA n := by
  intro n
  unfold inA
  have h_mod : (3 * n) % 3 = 0 := by rw [Nat.mul_mod_right]
  rw [h_mod]
  have h_lt : (0 : Nat) < 2 := by norm_num
  rw [if_pos h_lt]

-- L2 (sub-lemma): For (a' + 1) % 3 < 3, (a' + 1) % 3 / 3 = 0.
lemma div_mod_lt (m : Nat) (h : m < 3) : m / 3 = 0 := by
  omega

-- L3: If a > 0 and inA a, then a % 3 < 2 and inA (a / 3).
theorem inA_pos_implies (a : Nat) (ha : inA a) (hapos : a > 0) :
    a % 3 < 2 ∧ inA (a / 3) := by
  obtain ⟨n, hn⟩ : ∃ n, a = n + 1 := by
    cases a with
    | zero => simp at hapos
    | succ n => exact ⟨n, rfl⟩
  subst hn
  unfold inA at ha
  split_ifs at ha
  · exact ⟨‹_›, ha⟩
  · simp_all

-- L4 (main): For any a ∈ A and k with a < 3^k, we have 3^k + a ∈ A.
-- Proof: induction on a.
--   Base a = 0: 3^k + 0 = 3^k. By L_inA_3pow, inA (3^k).
--   Step a = a' + 1: inA (3^k + a' + 1).
--     By inA def: inA (3^k + a' + 1) = if (3^k + a' + 1) % 3 < 2 then inA ((3^k + a' + 1) / 3) else false.
--     (3^k + a' + 1) % 3 = (a' + 1) % 3 < 2 (since inA a).
--     (3^k + a' + 1) / 3 = 3^(k-1) + (a' + 1) / 3 (by integer division).
--     inA (3^(k-1) + (a' + 1) / 3).
--     By IH on a' + 1: inA a' + 1 implies inA (3^k + a' + 1) - same thing!
--     Wait that's not the right IH.
--     Use IH on (a' + 1) / 3. We have inA ((a' + 1) / 3) by L_inA_pos_implies.
--     And (a' + 1) / 3 < 3^(k-1) (from a < 3^k = 3 * 3^(k-1)).
--     So inA (3^(k-1) + (a' + 1) / 3) by IH.

-- Hmm. The induction is on a. But the IH is "inA a implies inA (3^k + a)".
-- For a = a' + 1, we'd use IH on a' (smaller than a).
-- But IH gives inA (3^k + a') (different from what we want).
-- 
-- Alternative: prove by induction on k. As before.

-- Let me try yet again with strong_induction_on k.

theorem inA_3pow_add_a (a k : Nat) (ha : inA a) (hak : a < 3^k) :
    inA (3^k + a) := by
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    -- Cases on k.
    cases k with
    | zero =>
      -- 3^0 = 1. a < 1 means a = 0.
      have ha_eq : a = 0 := by omega
      subst ha_eq
      -- inA 1 = true (by inA_3pow 0).
      exact inA_3pow 0
    | succ k' =>
      -- k = k' + 1. 3^k = 3 * 3^k'.
      rw [Nat.pow_succ]
      -- Goal: inA (3 * 3^k' + a).
      -- Cases on a.
      cases a with
      | zero =>
        -- a = 0. Goal: inA (3 * 3^k') = inA (3^k').
        -- Apply inA_3n_eq_n.
        rw [inA_3n_eq_n]
        -- Now need: inA (3^k'). By inA_3pow.
        exact inA_3pow k'
      | succ a' =>
        -- a = a' + 1. Use inA def.
        obtain ⟨ha_mod, ha_div⟩ := inA_pos_implies (a' + 1) ha (by omega)
        -- Apply IH with explicit arguments.
        have h1 : (a' + 1) / 3 < 3^k' := by
          rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
          exact hak
        -- The goal is to apply inA_3pow_add_a recursively with a = (a' + 1) / 3 and k = k'.
        -- But this requires unfolding inA first.
        -- Let's use a direct computation.
        -- Goal: inA (3 * 3^k' + (a' + 1))
        -- By inA def: = if (3 * 3^k' + (a' + 1)) % 3 < 2 then inA ((3 * 3^k' + (a' + 1)) / 3) else false.
        -- 3 * 3^k' ≡ 0 mod 3, so (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3 < 2.
        -- (3 * 3^k' + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3.
        -- So inA (3 * 3^k' + (a' + 1)) = inA (3^k' + (a' + 1) / 3).
        unfold inA
        have hmod_eq : (3 * 3^k' + (a' + 1)) % 3 = (a' + 1) % 3 := by
          rw [Nat.add_mod]; simp
        -- Normalize the goal's expression of (3 ^ k' * 3 + (a' + 1)) so it matches hmod_eq.
        rw [show ((3 ^ k' * 3).add a' + 1) = 3 ^ k' * 3 + (a' + 1) from by ring]
        have hmod_eq : (3 ^ k' * 3 + (a' + 1)) % 3 = (a' + 1) % 3 := by
          rw [Nat.mul_comm, Nat.add_mod]; simp
        rw [hmod_eq]
        -- Evaluate the if-condition using decide
        rw [if_pos ha_mod]
        -- Now: inA ((3 ^ k' * 3 + (a' + 1)) / 3)
        have hdiv_eq : (3 ^ k' * 3 + (a' + 1)) / 3 = 3^k' + (a' + 1) / 3 := by
          rw [Nat.mul_comm]
          rw [show (3 * 3^k' + (a' + 1)) = (a' + 1) + 3 * 3^k' from by ring]
          rw [Nat.div_add_mod]
          rw [Nat.mul_mod_right]; simp
          rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
          rw [div_mod_lt _ ha_mod]
          ring
        rw [hdiv_eq]
        have h_div_lt : (a' + 1) / 3 < 3^k' := by
          rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 3)]
          exact hak
        exact ih k' (by omega) ha_div h_div_lt

end Erdos125Induction
