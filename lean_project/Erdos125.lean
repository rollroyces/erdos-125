import Mathlib

namespace Erdos125

-- Definitions
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

-- Bijection
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

-- Tests of the bijection
example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 27 = inA 9 := inA_3n_eq_n 9
example : inA 81 = inA 27 := inA_3n_eq_n 27
example : inA (3 * 1000) = inA 1000 := inA_3n_eq_n 1000

-- The MAIN THEOREM: countA (3^k) = 2^k for all k.
-- We verify this for k = 0..10 using native_decide.
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

-- B: similar
def countB (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inB n then acc + 1 else acc) 0

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

example : countB 1 = 1 := by native_decide
example : countB 4 = 2 := by native_decide
example : countB 16 = 4 := by native_decide
example : countB 64 = 8 := by native_decide
example : countB 256 = 16 := by native_decide
example : countB 1024 = 32 := by native_decide
example : countB 4096 = 64 := by native_decide
example : countB 16384 = 128 := by native_decide

-- A + B
def countAB (N : Nat) : Nat :=
  let A := (List.range N).filter inA
  let B := (List.range N).filter inB
  let sums := A.flatMap fun a => B.map fun b => a + b
  (sums.filter (fun s => s < N)).eraseDups.length

example : countAB 100 = 98 := by native_decide
example : countAB 1000 = 857 := by native_decide
example : countAB 10000 = 9267 := by native_decide

end Erdos125