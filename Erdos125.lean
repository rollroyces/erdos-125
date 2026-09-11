import Mathlib

namespace Erdos125

-- Set A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Set B: integers with only digits 0, 1 in base 4
def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

-- Bijections
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

theorem inB_4n_eq_n : ∀ n : Nat, inB (4 * n) = inB n := by
  intro n
  cases n with
  | zero => rfl
  | succ k =>
    have h_eq1 : 4 * (k + 1) = 4 * k + 4 := by ring
    have h_eq2 : 4 * k + 4 = 4 * k + 3 + 1 := by ring
    rw [h_eq1, h_eq2, inB]
    have h_mod : (4 * k + 3 + 1) % 4 = 0 := by
      rw [show (4 * k + 3 + 1) = 4 * (k + 1) from by ring]
      rw [Nat.mul_mod_right]
    have h_div : (4 * k + 3 + 1) / 4 = k + 1 := by
      rw [show (4 * k + 3 + 1) = 4 * (k + 1) from by ring]
      exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 3)
    rw [h_mod, h_div]
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

theorem inB_4m_2_eq_false : ∀ m : Nat, inB (4 * m + 2) = false := by
  intro m
  have h_eq : 4 * m + 2 = 4 * m + 1 + 1 := by ring
  rw [h_eq, inB]
  have h_mod : (4 * m + 1 + 1) % 4 = 2 := by omega
  rw [h_mod]
  have h_neg : ¬ (2 < 2) := by omega
  simp [h_neg]

theorem inB_4m_3_eq_false : ∀ m : Nat, inB (4 * m + 3) = false := by
  intro m
  have h_eq : 4 * m + 3 = 4 * m + 2 + 1 := by ring
  rw [h_eq, inB]
  have h_mod : (4 * m + 2 + 1) % 4 = 3 := by omega
  rw [h_mod]
  have h_neg : ¬ (3 < 2) := by omega
  simp [h_neg]

-- countA, countB
def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

def countB (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inB n then acc + 1 else acc) 0

theorem countA_succ (N : Nat) : countA (N + 1) = countA N + (if inA N then 1 else 0) := by
  unfold countA
  rw [List.range_succ]
  simp [List.foldl_append]
  by_cases h : inA N
  · simp [h]
  · simp [h]

theorem countB_succ (N : Nat) : countB (N + 1) = countB N + (if inB N then 1 else 0) := by
  unfold countB
  rw [List.range_succ]
  simp [List.foldl_append]
  by_cases h : inB N
  · simp [h]
  · simp [h]

-- KEY LEMMA for A: countA (3 * N) = 2 * countA N
theorem countA_3mul_eq_2mul (N : Nat) : countA (3 * N) = 2 * countA N := by
  induction N using Nat.rec with
  | zero => rfl
  | succ N' ih =>
    have h_eq : 3 * (N' + 1) = 3 * N' + 3 := by ring
    rw [h_eq]
    rw [countA_succ, countA_succ, countA_succ]
    rw [ih]
    rw [inA_3n_eq_n N']
    have h_3N1 : inA (3 * N' + 1) = inA N' := by
      have h1 : (3 * N' + 1) % 3 = 1 := by omega
      have h2 : (3 * N' + 1) / 3 = N' := by omega
      rw [inA, h1, h2]
      have h_lt : (1 : Nat) < 2 := by norm_num
      simp [h_lt]
    rw [h_3N1]
    rw [inA_3m_2_eq_false N']
    have h_false : (if false = true then (1 : Nat) else 0) = 0 := by simp
    rw [h_false]
    rw [countA_succ]
    ring

-- KEY LEMMA for B: countB (4 * N) = 2 * countB N
-- Note: 4*(N+1) has 4 new elements, but only 2 of them (4N, 4N+1) are in B.
-- So countB (4 * (N' + 1)) = countB (4 * N') + 2 * inB N' = 2 * countB N' + 2 * inB N'
--   = 2 * (countB N' + inB N') = 2 * countB (N' + 1)
theorem countB_4mul_eq_2mul (N : Nat) : countB (4 * N) = 2 * countB N := by
  induction N using Nat.rec with
  | zero => rfl
  | succ N' ih =>
    have h_eq : 4 * (N' + 1) = 4 * N' + 4 := by ring
    rw [h_eq]
    rw [countB_succ, countB_succ, countB_succ, countB_succ]
    rw [ih]
    rw [inB_4n_eq_n N']
    have h_4N1 : inB (4 * N' + 1) = inB N' := by
      have h1 : (4 * N' + 1) % 4 = 1 := by omega
      have h2 : (4 * N' + 1) / 4 = N' := by omega
      rw [inB, h1, h2]
      have h_lt : (1 : Nat) < 2 := by norm_num
      simp [h_lt]
    rw [h_4N1]
    rw [inB_4m_2_eq_false N', inB_4m_3_eq_false N']
    have h_false : (if false = true then (1 : Nat) else 0) = 0 := by simp
    rw [h_false]
    -- Apply countB_succ twice to group the new terms
    rw [countB_succ]
    ring

-- Main theorems
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

theorem countB_4pow_eq_2pow : ∀ k : Nat, countB (4^k) = 2^k := by
  intro k
  induction k using Nat.rec with
  | zero => native_decide
  | succ k' ih =>
    have h_eq : 4 ^ (k' + 1) = 4 * 4 ^ k' := by ring
    rw [h_eq]
    rw [countB_4mul_eq_2mul (4 ^ k')]
    rw [ih]
    omega

-- Tests
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide

example : countB 1 = 1 := by native_decide
example : countB 4 = 2 := by native_decide
example : countB 16 = 4 := by native_decide
example : countB 64 = 8 := by native_decide
example : countB 256 = 16 := by native_decide

example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 2 = false := inA_3m_2_eq_false 0
example : inA 5 = false := inA_3m_2_eq_false 1

example : inB 4 = inB 1 := inB_4n_eq_n 1
example : inB 16 = inB 4 := inB_4n_eq_n 4
example : inB 2 = false := inB_4m_2_eq_false 0
example : inB 3 = false := inB_4m_3_eq_false 0

end Erdos125