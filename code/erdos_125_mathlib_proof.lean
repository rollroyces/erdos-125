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

-- countA_in_range lo hi: |A ∩ [lo, hi)| (with lo ≤ hi)
def countA_in_range (lo hi : Nat) : Nat :=
  ((List.range hi).filter (fun n => lo ≤ n ∧ inA n)).length

-- countA in [3^k, 2*3^k) = countA in [0, 3^k) for any k.
-- Proof: n in [3^k, 2*3^k) means n = 3^k + r, r in [0, 3^k). 
-- inA n = inA (3^k + r). But the bijection is for inA (3 * n) = inA n, i.e., multiplication by 3.
-- The map r → 3^k + r is ADDING 3^k, not multiplying. So we can't directly use the bijection.
-- Wait: 3^k + r, with k fixed, is just shifting r. So inA (3^k + r) should depend on r.
-- Hmm, this is the digit check. The lowest digit of 3^k + r is r mod 3 (if r < 3^k).
-- So inA (3^k + r) checks r mod 3 first, then proceeds. This is NOT the same as inA r.
-- Actually, the bijection is inA (3 * r) = inA r. So if we want to count 3^k + r for r in [0, 3^k),
-- we're not in the bijection range.
-- Let me reconsider the induction.
-- The cleanest argument: for k → k+1, we have countA (3 * 3^k) = countA (3^(k+1)).
-- But inA (3 * n) = inA n says the set {3n : n in A} = A. So A is closed under 3x.
-- We need: A is also closed under shift: A = 3A. Then A = 3A = ... = 3^k A. And A ∩ [0, 3^k) = 3^k (A ∩ [0, 1)) = 3^k {0}? 
-- Wait, that doesn't work because A is not closed under shift.

-- Let me reconsider. The actual bijection is: A = 3A (multiplication by 3 preserves A).
-- So |A ∩ [0, 3^(k+1))| = |A ∩ [0, 3) ∪ A ∩ [3, 9) ∪ ... ∪ A ∩ [3^k * 3, 3^(k+1))|
-- Hmm, that's not the right decomposition.

-- Actually the right structure:
-- [0, 3^(k+1)) = {0, 1, ..., 3^(k+1) - 1}
-- The base-3 representation of any n in this range has k+1 digits.
-- Write n = d_k * 3^k + r where 0 ≤ d_k ≤ 2 and 0 ≤ r < 3^k.
-- n ∈ A iff d_k ∈ {0, 1} and r ∈ A (by induction on the lower digits).
-- So countA (3^(k+1)) = sum over d_k in {0, 1, 2} of countA (3^k) when d_k = 0 or 1
--                                            of 0 when d_k = 2.
-- Wait that's not right either. Let me think more carefully.
-- A ∩ [0, 3^(k+1)) = {n : n < 3^(k+1), inA n}
-- For such n, write n = d_k * 3^k + r where 0 ≤ d_k ≤ 2 and 0 ≤ r < 3^k.
-- inA n iff inA r AND d_k ∈ {0, 1}.
-- (Because inA n = (n mod 3 < 2) && inA (n / 3), and n mod 3 = r mod 3, n / 3 = d_{k-1} * 3^{k-1} + ... = r / 3.)
-- Hmm wait, that's only one step. inA n = (r mod 3 < 2) && inA (something).
-- The full recursion: inA n = inA r where r is the number obtained by dropping the lowest digit,
-- and we need n mod 3 < 2.
-- For n = d_k * 3^k + r: inA n = (r mod 3 < 2) && inA (d_{k-1} * 3^{k-1} + ...).
-- So inA n depends on r and the leading digit doesn't directly affect the FIRST check.
-- The leading digit affects later checks (after dropping k low digits).

-- OK so the leading digit DOES matter. Let me reconsider:
-- inA n = (n mod 3 < 2) && inA (n / 3)
-- = (r mod 3 < 2) && inA (d_k * 3^(k-1) + r')  where r' = r / 3 (since n = 3 * (d_k * 3^(k-1) + r') + (r mod 3))
-- = (r mod 3 < 2) && inA (d_k * 3^(k-1) + r')
-- Iterating: inA n = (r_0 < 2) && (r_1 < 2) && ... && (r_{k-1} < 2) && inA (d_k)
-- where r_0 = r mod 3, r_1 = (r / 3) mod 3, ..., and d_k is the final "value" after dropping k+1 digits.
-- inA d_k: this requires d_k = 0 (since inA 0 = true, inA 1 = true, inA 2 = false, etc., inA m is inA m for m small).
-- Wait, d_k is a digit (0, 1, or 2). inA 0 = true, inA 1 = true, inA 2 = false.
-- So the final inA d_k = (d_k = 0) ∨ (d_k = 1) = (d_k < 2).
-- So inA n = (all k+1 digits are 0 or 1).

-- So the structure of A in [0, 3^(k+1)):
-- n has k+1 base-3 digits: d_k d_{k-1} ... d_0.
-- n ∈ A iff d_0, d_1, ..., d_k are all 0 or 1.
-- Number of such (k+1)-digit numbers: 2^(k+1).
-- This is the L1 lemma.

-- The bijection argument:
-- Define f: {0, 1}^k → A ∩ [0, 3^k) by f(b_0 b_1 ... b_{k-1}) = sum b_i * 3^i
-- This is a bijection. We just proved |A ∩ [0, 3^k)| = 2^k for k = 0, 1, ..., 10 via native_decide.
-- We can state this as a theorem and prove it by induction (which we have).

-- The cleanest way to formalize the bijection:
-- 1. For k = 0: |A ∩ [0, 1)| = 1 (just {0})
-- 2. For k → k+1:
--    A ∩ [0, 3^(k+1)) = {n in [0, 3^(k+1)) : all digits in {0, 1}}
--    We split based on the lowest digit:
--    - n mod 3 = 0: n / 3 is in A ∩ [0, 3^k) → count = |A ∩ [0, 3^k)| = 2^k
--    - n mod 3 = 1: n / 3 is in A ∩ [0, 3^k) → count = 2^k
--    - n mod 3 = 2: 0
--    Total: 2 * 2^k = 2^(k+1)

-- This is cleaner because it uses the LOWEST digit, not the leading digit.
-- The bijection: A = 3A ∪ (3A + 1), and (3A + 2) ∩ [0, 3^(k+1)) ⊆ complement of A.

-- Let me prove: countA (3 * N) = 2 * countA N for all N.
-- Proof: A ∩ [0, 3N) = {3m : m ∈ A ∩ [0, N)} ∪ {3m + 1 : m ∈ A ∩ [0, N)}.
-- The set {3m + 2 : m} has no elements in A (inA (3m+2) = false).
-- So |A ∩ [0, 3N)| = 2 * |A ∩ [0, N)| = 2 * countA N.
-- This uses inA_3n_eq_n and inA_3m_2_eq_false.

-- To use this, we need: countA (3^k) = countA (3 * 3^(k-1)) = 2 * countA (3^(k-1)).
-- And we need the base case: countA 1 = 1.
-- So by induction: countA (3^k) = 2^k.

-- We need to be careful: countA N = |A ∩ [0, N)| is computed by List.range, not by direct set.
-- So we need to show: the list elements that satisfy n in A are exactly the elements of A.

-- For the induction, we use:
-- countA (3^(k+1)) = countA (3 * 3^k) = 2 * countA (3^k) = 2 * 2^k = 2^(k+1)
-- The middle step (countA (3 * 3^k) = 2 * countA (3^k)) is what we need to prove.

-- A cleaner way to formalize this:
-- Define: A_elements (n : Nat) : List Nat := [m : m < n, inA m]
-- countA n = A_elements n |>.length
-- Or use List.count: countA n = (List.range n).count inA

-- Let me state the theorem properly and try to close the induction:
theorem countA_3pow_eq_2pow : ∀ k : Nat, countA (3^k) = 2^k := by
  intro k
  induction k using Nat.rec with
  | zero =>
    -- 3^0 = 1, countA 1 = 1 = 2^0
    native_decide
  | succ k' ih =>
    -- countA (3^(k'+1)) = countA (3 * 3^k')
    have h_eq : 3 ^ (k' + 1) = 3 * 3 ^ k' := by ring
    rw [h_eq]
    -- We need to show countA (3 * 3^k') = 2 * countA (3^k').
    -- This is the bijection step: A ∩ [0, 3N) = 3A ∩ [0, 3N) ∪ (3A+1) ∩ [0, 3N)
    --                                         = {3m : m ∈ A, 3m < 3N} ∪ {3m+1 : m ∈ A, 3m+1 < 3N}
    -- The size: 2 * |{m ∈ A : m < N}| = 2 * countA N.
    sorry

-- Tests
example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 27 = inA 9 := inA_3n_eq_n 9
example : inA 2 = false := inA_3m_2_eq_false 0
example : inA 5 = false := inA_3m_2_eq_false 1
example : inA 8 = false := inA_3m_2_eq_false 2

example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide

end Erdos125