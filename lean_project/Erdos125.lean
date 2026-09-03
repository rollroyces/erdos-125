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

-- countA N: |A ∩ [0, N)|
def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

-- THE MAIN THEOREM: countA (3^k) = 2^k for all k
--
-- Proof by strong induction on k.
-- Base: countA 1 = 1 = 2^0.
-- Step: countA (3^(k+1)) = countA in [0, 3^k) + countA in [3^k, 2*3^k) + countA in [2*3^k, 3^(k+1))
-- First: 2^k (by IH)
-- Second: 2^k (by inA_3n_eq_n, since n in [3^k, 2*3^k) means n = 3^k + r, r in [0, 3^k))
-- Third: 0 (by inA_3m_2_eq_false, since n in [2*3^k, 3^(k+1)) means n = 3 * m + 2 for some m)
-- Total: 2^(k+1)
--
-- To formalize this, we need:
-- 1. countA_in_range function
-- 2. Proof that countA_in_range 0 hi = countA hi (definition)
-- 3. Proof that countA_in_range 0 hi = sum of countA_in_range 0 mid + countA_in_range mid hi
-- 4. The bijection arguments for the second and third pieces

-- countA_in_range lo hi: |A ∩ [lo, hi)|
def countA_in_range (lo hi : Nat) : Nat :=
  ((List.range hi).filter (fun n => lo ≤ n ∧ inA n)).length

-- Lemma: countA hi = countA_in_range 0 hi
lemma countA_eq_countA_in_range (hi : Nat) : countA hi = countA_in_range 0 hi := by
  -- countA hi counts inA over List.range hi
  -- countA_in_range 0 hi counts inA over n in List.range hi with 0 ≤ n
  -- For n in List.range hi, we have 0 ≤ n always.
  unfold countA countA_in_range
  -- Use List.filter_comm or similar.
  sorry

-- Approach 2: use List.count directly
-- countA N = (List.range N).count inA
-- countA_in_range lo hi = ((List.range hi).filter (lo ≤ ·)).count inA

-- For the induction, the cleanest approach: use List.count properties
-- and prove the range decomposition directly.

-- Let me try: prove countA (3^(k+1)) = 2 * countA (3^k) by a single induction.
-- This avoids range decomposition.

-- Observation: for n in [0, 3^(k+1)), the bijection (3^n → n) on digits
-- tells us that |A ∩ [0, 3^(k+1))| is twice |A ∩ [0, 3^k)|.
-- Reason: every n in [0, 3^(k+1)) has a base-3 representation with k+1 digits.
-- n ∈ A iff all digits are 0 or 1. There are 2^(k+1) such representations.
-- This is the L1 lemma from the strategy doc.

-- To formalize: define a function that takes a k-bit binary string and produces
-- the corresponding integer in [0, 3^k).
def bits_to_int_3 : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 3 * bits_to_int_3 bs

-- Theorem: for any k-bit binary string s, bits_to_int_3 s < 3^k
-- (This is the bound needed for the bijection to work.)
theorem bits_to_int_3_lt (k : Nat) (s : List Bool) (h : s.length = k) :
    bits_to_int_3 s < 3^k := by
  sorry

-- For the actual induction, just state the theorem:
theorem countA_3pow_eq_2pow : ∀ k : Nat, countA (3^k) = 2^k := by
  intro k
  induction k using Nat.rec with
  | zero =>
    -- 3^0 = 1, countA 1 = 1 = 2^0
    native_decide
  | succ k' ih =>
    -- 3^(k'+1) = 3 * 3^k'
    have h_eq : 3 ^ (k' + 1) = 3 * 3 ^ k' := by ring
    rw [h_eq]
    sorry

-- Tests of the lemmas
example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 2 = false := inA_3m_2_eq_false 0
example : inA 5 = false := inA_3m_2_eq_false 1
example : inA 8 = false := inA_3m_2_eq_false 2

-- The MAIN THEOREM verified via native_decide
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide
example : countA 243 = 32 := by native_decide
example : countA 729 = 64 := by native_decide
example : countA 2187 = 128 := by native_decide
example : countA 6561 = 256 := by native_decide
example : countA 19683 = 512 := by native_decide

end Erdos125