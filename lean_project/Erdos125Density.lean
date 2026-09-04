import Mathlib

namespace Erdos125Density

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- B: integers with only digits 0, 1 in base 4
def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

-- Count A ∩ [0, N)
def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

-- Count B ∩ [0, N)
def countB (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inB n then acc + 1 else acc) 0

-- Count A ∩ [N, 2N): needed for sumset
def countA_in_range (N : Nat) : Nat :=
  (List.range (2 * N)).foldl (fun acc n => if N ≤ n ∧ n < 2 * N ∧ inA n then acc + 1 else acc) 0

-- Count B ∩ [0, 2N)
def countB_in_range (N : Nat) : Nat :=
  (List.range (2 * N)).foldl (fun acc n => if inB n then acc + 1 else acc) 0

-- Count distinct sums a + b for a ∈ A ∩ [N, 2N), b ∈ B ∩ [0, 2N), with a + b ∈ [N, 2N).
-- Use list.eraseDup to remove duplicates.
def countAB_distinct (N : Nat) : Nat :=
  let A_list := ((List.range (2 * N)).filter (fun n => N ≤ n ∧ n < 2 * N ∧ inA n))
  let B_list := ((List.range (2 * N)).filter inB)
  let raw_sums := A_list.foldl (fun acc a =>
    B_list.foldl (fun acc' b =>
      let s := a + b
      if N ≤ s ∧ s < 2 * N then acc'.concat s else acc') acc) []
  raw_sums.eraseDup.length

-- Test countA matches 2^k for N = 3^k
example : countA 3 = 2 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide
example : countA 243 = 32 := by native_decide
example : countA 729 = 64 := by native_decide
example : countA 2187 = 128 := by native_decide
example : countA 6561 = 256 := by native_decide
example : countA 19683 = 512 := by native_decide

-- Test countB matches 2^m for N = 4^m
example : countB 4 = 2 := by native_decide
example : countB 16 = 4 := by native_decide
example : countB 64 = 8 := by native_decide
example : countB 256 = 16 := by native_decide
example : countB 1024 = 32 := by native_decide
example : countB 4096 = 64 := by native_decide

-- Test countAB_distinct for small N (less computationally expensive)
example : countAB_distinct 3 = 3 := by native_decide
example : countAB_distinct 9 = 9 := by native_decide
example : countAB_distinct 27 = 27 := by native_decide
example : countAB_distinct 81 = 79 := by native_decide

-- For density > 0.5 verification (2 * count > N):
example : 2 * countAB_distinct 81 > 81 := by native_decide
example : 2 * countAB_distinct 27 > 27 := by native_decide

end Erdos125Density
