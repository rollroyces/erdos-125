import Mathlib

namespace Erdos125

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Arithmetic: (3 * n) mod 3 = 0 and (3 * n) / 3 = n
theorem three_mul_mod (n : Nat) : (3 * n) % 3 = 0 := by
  rw [Nat.mul_mod_right]

theorem three_mul_div (n : Nat) : (3 * n) / 3 = n := by
  exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 2)

-- KEY LEMMA: inA (3 * n) = inA n for all n.
-- This is the bijection that Erdős 125 needs.
-- Proof: For n = 0, trivial. For n = k+1, 3(k+1) = 3k+3, unfolds to
-- ((3k+3) % 3 < 2) && inA ((3k+3)/3) = (0 < 2) && inA (k+1) = inA (k+1).
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
      exact three_mul_mod (k + 1)
    have h_div : (3 * k + 2 + 1) / 3 = k + 1 := by
      rw [show (3 * k + 2 + 1) = 3 * (k + 1) from by ring]
      exact three_mul_div (k + 1)
    rw [h_mod, h_div]
    -- Now: (if 0 < 2 then inA (k + 1) else false) = inA (k + 1)
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

-- Test the lemma
example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 27 = inA 9 := inA_3n_eq_n 9
example : inA 81 = inA 27 := inA_3n_eq_n 27
example : inA (3 * 1000) = inA 1000 := inA_3n_eq_n 1000

-- B: integers with only digits 0, 1 in base 4
def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

-- Arithmetic: (4 * n) mod 4 = 0 and (4 * n) / 4 = n
theorem four_mul_mod (n : Nat) : (4 * n) % 4 = 0 := by
  rw [Nat.mul_mod_right]

theorem four_mul_div (n : Nat) : (4 * n) / 4 = n := by
  exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 3)

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
      exact four_mul_mod (k + 1)
    have h_div : (4 * k + 3 + 1) / 4 = k + 1 := by
      rw [show (4 * k + 3 + 1) = 4 * (k + 1) from by ring]
      exact four_mul_div (k + 1)
    rw [h_mod, h_div]
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

-- countA N: |A ∩ [0, N)|
def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

def countB (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inB n then acc + 1 else acc) 0

-- The Erdős 125 counting lemma: |A ∩ [0, 3^k)| = 2^k
-- This is a COROLLARY of the bijection: every n in [0, 3^k) has a unique
-- base-3 representation with k digits (allowing leading zeros). n ∈ A iff
-- all digits are in {0, 1}. The number of such representations is 2^k.
--
-- We can prove this by induction: for k = 0, |A ∩ [0, 1)| = 1 = 2^0.
-- For k + 1, split [0, 3^(k+1)) into [0, 3^k), [3^k, 2·3^k), [2·3^k, 3^(k+1)):
--   [0, 3^k): by IH, count = 2^k
--   [3^k, 2·3^k): n = 3^k + r, r in [0, 3^k). n ∈ A iff r ∈ A (by inA_3n_eq_n).
--   [2·3^k, 3^(k+1)): leading digit is 2, so no n ∈ A.
-- Total: 2^k + 2^k + 0 = 2^(k+1).
--
-- This is the MAIN THEOREM. The full proof requires defining countA carefully
-- and proving the range decomposition. Below we verify the count for small k.
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
example : countA 59049 = 1024 := by native_decide

example : countB 1 = 1 := by native_decide
example : countB 4 = 2 := by native_decide
example : countB 16 = 4 := by native_decide
example : countB 64 = 8 := by native_decide
example : countB 256 = 16 := by native_decide
example : countB 1024 = 32 := by native_decide
example : countB 4096 = 64 := by native_decide
example : countB 16384 = 128 := by native_decide

-- A + B count
def countAB (N : Nat) : Nat :=
  let A := (List.range N).filter inA
  let B := (List.range N).filter inB
  let sums := A.flatMap fun a => B.map fun b => a + b
  (sums.filter (fun s => s < N)).eraseDups.length

example : countAB 100 = 98 := by native_decide
example : countAB 1000 = 857 := by native_decide
example : countAB 10000 = 9267 := by native_decide

end Erdos125