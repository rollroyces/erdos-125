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

-- Count A ∩ [N, 2N): needed for sumset
def countA_in_range (N : Nat) : Nat :=
  ((List.range (2 * N)).filter (fun n => N ≤ n ∧ n < 2 * N ∧ inA n)).length

-- Count B ∩ [0, 2N)
def countB_in_range (N : Nat) : Nat :=
  ((List.range (2 * N)).filter inB).length

-- Test countA_in_range
example : countA_in_range 3 = 2 := by native_decide  -- A ∩ [3, 6): {3, 4}
example : countA_in_range 27 = 8 := by native_decide
example : countA_in_range 81 = 16 := by native_decide
example : countA_in_range 243 = 32 := by native_decide
example : countA_in_range 729 = 64 := by native_decide
example : countA_in_range 2187 = 128 := by native_decide

-- Test countB_in_range
example : countB_in_range 4 = 4 := by native_decide   -- B ∩ [0, 8): 0, 1, 4, 5
example : countB_in_range 32 = 8 := by native_decide   -- B ∩ [0, 64): 0, 1, 4, 5, 16, 17, 20, 21
example : countB_in_range 128 = 16 := by native_decide  -- B ∩ [0, 256)
example : countB_in_range 512 = 32 := by native_decide  -- B ∩ [0, 1024)
example : countB_in_range 2048 = 64 := by native_decide  -- B ∩ [0, 4096) (B is bounded, max B < 4096)

end Erdos125Density
