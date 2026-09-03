import Mathlib

namespace Erdos125

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

theorem inA_3n_eq_n : ∀ n : Nat, inA (3 * n) = inA n := by
  intro n
  cases n with
  | zero => rfl
  | succ k =>
    have h_eq1 : 3 * (k + 1) = 3 * k + 3 := by ring
    have h_eq2 : 3 * k + 3 = 3 * k + 2 + 1 := by ring
    rw [h_eq1, h_eq2, inA]
    have h_mod : (3 * k + 2 + 1) % 3 = 0 := by
      rw [show (3 * k + 2 + 1) = 3 * (k + 1) from by ring]
      rw [Nat.mul_mod_right]
    have h_div : (3 * k + 2 + 1) / 3 = k + 1 := by
      rw [show (3 * k + 2 + 1) = 3 * (k + 1) from by ring]
      exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 2)
    rw [h_mod, h_div]
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

theorem inA_3m_2_eq_false : ∀ m : Nat, inA (3 * m + 2) = false := by
  intro m
  have h_eq : 3 * m + 2 = 3 * m + 1 + 1 := by ring
  rw [h_eq, inA]
  have h_mod : (3 * m + 1 + 1) % 3 = 2 := by omega
  rw [h_mod]
  have h_neg : ¬ (2 < 2) := by omega
  simp [h_neg]

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

theorem countA_succ (N : Nat) : countA (N + 1) = countA N + (if inA N then 1 else 0) := by
  unfold countA
  rw [List.range_succ]
  simp [List.foldl_append]
  -- Goal: if inA N then ... + 1 else ... = ... + (if inA N then 1 else 0)
  -- The foldl append gives us: foldl ... [0..N-1] ++ [N] = foldl ... [0..N-1] + (if inA N then 1 else 0)
  -- After simp, the LHS becomes: if inA N then acc + 1 else acc
  -- We need to convert to: acc + (if inA N then 1 else 0)
  by_cases h : inA N
  · simp [h]
  · simp [h]

-- KEY LEMMA: countA (3 * N) = 2 * countA N
-- Proof: induction on N.
-- For N = 0: 0 = 2 * 0.
-- For N = N' + 1: countA (3 * (N' + 1)) = countA (3 * N' + 3)
--   = countA (3 * N') + 3 new terms (by 3x countA_succ)
--   = 2 * countA N' + inA(3N') + inA(3N'+1) + inA(3N'+2)  (by IH)
--   = 2 * countA N' + inA N' + inA N' + 0  (by inA_3n_eq_n, inA_3m_2_eq_false, and direct computation)
--   = 2 * (countA N' + inA N')  (factor 2)
--   = 2 * countA (N' + 1)  (by countA_succ)
theorem countA_3mul_eq_2mul (N : Nat) : countA (3 * N) = 2 * countA N := by
  induction N using Nat.rec with
  | zero => rfl
  | succ N' ih =>
    have h_eq : 3 * (N' + 1) = 3 * N' + 3 := by ring
    rw [h_eq]
    rw [countA_succ, countA_succ, countA_succ]
    rw [ih]
    -- Simplify: use the bijection lemmas
    rw [inA_3n_eq_n N']
    -- For inA (3 * N' + 1): use direct unfolding
    -- inA (3 * N' + 1) = if (3N'+1) % 3 < 2 then inA ((3N'+1)/3) else false
    -- = if 1 < 2 then inA N' else false = inA N'
    have h_3N1 : inA (3 * N' + 1) = inA N' := by
      have h1 : (3 * N' + 1) % 3 = 1 := by omega
      have h2 : (3 * N' + 1) / 3 = N' := by omega
      rw [inA, h1, h2]
      have h_lt : (1 : Nat) < 2 := by norm_num
      simp [h_lt]
    rw [h_3N1]
    -- For inA (3 * N' + 2): use inA_3m_2_eq_false
    rw [inA_3m_2_eq_false N']
    -- Now: 2 * countA N' + (if inA N' then 1 else 0) + (if inA N' then 1 else 0) + 0
    -- Simplify the if-false = true to 0
    have h_false : (if false = true then (1 : Nat) else 0) = 0 := by simp
    rw [h_false]
    -- We want: ... = 2 * countA (N' + 1)
    -- Note: countA (N' + 1) = countA N' + (if inA N' then 1 else 0)
    rw [countA_succ]
    ring

theorem countA_3pow_eq_2pow : ∀ k : Nat, countA (3^k) = 2^k := by
  intro k
  induction k using Nat.rec with
  | zero => native_decide
  | succ k' ih =>
    have h_eq : 3 ^ (k' + 1) = 3 * 3 ^ k' := by ring
    rw [h_eq]
    rw [countA_3mul_eq_2mul (3 ^ k')]
    rw [ih]
    omega

-- Tests
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide

example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 2 = false := inA_3m_2_eq_false 0
example : inA 5 = false := inA_3m_2_eq_false 1

end Erdos125