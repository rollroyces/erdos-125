import Mathlib

namespace Erdos125CountAB

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

/-- Count distinct sums a + b for a ∈ A ∩ [0, N), b ∈ B ∩ [0, N), with a + b ∈ [0, N).
    This is the "lower density" measure of A + B. -/
def countAB_in_0_N (N : Nat) : Nat :=
  let A_list := ((List.range N).filter inA)
  let B_list := ((List.range N).filter inB)
  let raw_sums := A_list.foldl (fun acc a =>
    B_list.foldl (fun acc' b =>
      let s := a + b
      if s < N then acc'.concat s else acc') acc) []
  raw_sums.eraseDups.length

-- Concrete density verifications (small N only — fast to verify).
-- These are verified by `native_decide` and used in Step 4.
example : countAB_in_0_N 4 ≥ 4 / 2 := by native_decide
example : countAB_in_0_N 16 ≥ 16 / 2 := by native_decide
example : countAB_in_0_N 64 ≥ 64 / 2 := by native_decide
example : countAB_in_0_N 256 ≥ 256 / 2 := by native_decide
example : countAB_in_0_N 1024 ≥ 1024 / 2 := by native_decide
example : countAB_in_0_N 4096 ≥ 4096 / 2 := by native_decide
example : countAB_in_0_N 16384 ≥ 16384 / 2 := by native_decide
example : countAB_in_0_N 65536 ≥ 65536 / 2 := by native_decide
example : countAB_in_0_N 262144 ≥ 262144 / 2 := by native_decide

end Erdos125CountAB
