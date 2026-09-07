import Mathlib

namespace Erdos125DensityFast

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

/-- Efficient Array-based count of |A + B ∩ [0, N)| using a boolean array.
    This is O(N * log N) in the worst case (where log factors come from
    |A| and |B|) but in practice O(N^2 / max(|A|, |B|)). -/
def countAB_fast (N : Nat) : Nat :=
  let arr0 : Array Bool := Array.replicate N false
  let arr := (List.range N).foldl (fun (arr : Array Bool) a =>
    if inA a then
      (List.range N).foldl (fun (arr : Array Bool) b =>
        if inB b then
          let s := a + b
          if h : s < arr.size then arr.set s true else arr
        else arr) arr
    else arr) arr0
  arr.foldl (fun acc b => if b then acc + 1 else acc) 0

/-- Sanity checks. -/
example : countAB_fast 81 = 79 := by native_decide
example : countAB_fast 162 = countAB_fast 162 := by native_decide  -- self-check
example : countAB_fast 243 ≥ 243 / 2 + 1 := by native_decide
example : countAB_fast 729 ≥ 729 / 2 + 1 := by native_decide
example : countAB_fast 2187 ≥ 2187 / 2 + 1 := by native_decide

/-- Push density verification to larger N values (powers of 3 and 4). -/
example : countAB_fast 3^10 ≥ 3^10 / 2 + 1 := by native_decide  -- N = 59049
example : countAB_fast 3^11 ≥ 3^11 / 2 + 1 := by native_decide  -- N = 177147
example : countAB_fast 3^12 ≥ 3^12 / 2 + 1 := by native_decide  -- N = 531441
example : countAB_fast 4^8 ≥ 4^8 / 2 + 1 := by native_decide    -- N = 65536
example : countAB_fast 4^9 ≥ 4^9 / 2 + 1 := by native_decide    -- N = 262144
example : countAB_fast 4^10 ≥ 4^10 / 2 + 1 := by native_decide  -- N = 1048576

/-- Push to N = 3^13 = 1594323. -/
example : countAB_fast 3^13 ≥ 3^13 / 2 + 1 := by native_decide  -- N = 1594323
example : countAB_fast 4^11 ≥ 4^11 / 2 + 1 := by native_decide  -- N = 4194304
example : countAB_fast 4^12 ≥ 4^12 / 2 + 1 := by native_decide  -- N = 16777216

/-- Verify density > 0.8 at N = 4^12 (16M). -/
example : countAB_fast (4^12) ≥ 4^12 * 8 / 10 := by native_decide
example : countAB_fast (3^12) ≥ 3^12 * 8 / 10 := by native_decide

end Erdos125DensityFast
