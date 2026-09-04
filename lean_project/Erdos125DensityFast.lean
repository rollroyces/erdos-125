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

-- Efficient Array-based count of |A + B ∩ [0, N)|.
-- Uses a boolean array indexed by sum value.
def countAB_fast (N : Nat) : Nat :=
  -- Initialize array of size N with false
  let arr0 : Array Bool := Array.mkArray N false
  -- For each a in A ∩ [0, N), for each b in B ∩ [0, N), set arr[a+b] = true if a+b < N
  let arr := (List.range N).foldl (fun (arr : Array Bool) a =>
    if inA a then
      (List.range N).foldl (fun (arr : Array Bool) b =>
        if inB b then
          let s := a + b
          if h : s < arr.size then arr.set s true else arr
        else arr) arr
    else arr) arr0
  -- Count true entries
  arr.foldl (fun acc b => if b then acc + 1 else acc) 0

-- Tests
#guard countAB_fast 81 = 79

end Erdos125DensityFast
