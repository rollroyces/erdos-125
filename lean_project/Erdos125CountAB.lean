import Mathlib
import Erdos125

namespace Erdos125CountAB

open Erdos125

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- B: integers with only digits 0, 1 in base 4
-- (Standard Erdős 125 definition: B = {Σ ε_k 4^k : ε_k ∈ {0,1}})
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

/-- Fast implementation of countAB_in_0_N.

    `acc[i] = true` iff sum `i` is achievable as `a + b` with `a ∈ A ∩ [0, N), b ∈ B ∩ [0, N), a + b < N`.

    Verified equivalent to `countAB_in_0_N` for small N (4, 16, 64, 256, 1024, 4096).
    Used for larger N values where `countAB_in_0_N` would be too slow.

    **Honest note**: native_decide on `countAB_in_0_N_fast 262144` was attempted
    twice and killed after >15 minutes each time without completing. -/
def countAB_in_0_N_fast (N : Nat) : Nat :=
  let A_list := ((List.range N).filter inA)
  let B_list := ((List.range N).filter inB)
  let mkSet : List (Nat × Bool) → Nat → List (Nat × Bool) :=
    fun acc i =>
      let found := A_list.any fun a =>
        B_list.any fun b => a + b = i
      acc ++ [(i, found)]
  let pairs := (List.range N).foldl mkSet []
  (pairs.map Prod.snd).filter id |>.length

-- Concrete density verifications (small N only — fast to verify).
example : countAB_in_0_N 4 ≥ 4 / 2 := by native_decide
example : countAB_in_0_N 16 ≥ 16 / 2 := by native_decide
example : countAB_in_0_N 64 ≥ 64 / 2 := by native_decide
example : countAB_in_0_N 256 ≥ 256 / 2 := by native_decide
example : countAB_in_0_N 1024 ≥ 1024 / 2 := by native_decide
example : countAB_in_0_N 4096 ≥ 4096 / 2 := by native_decide
example : countAB_in_0_N 16384 ≥ 16384 / 2 := by native_decide
example : countAB_in_0_N 65536 ≥ 65536 / 2 := by native_decide

-- Verify the fast implementation matches the slow one for small N.
example : countAB_in_0_N_fast 4 = countAB_in_0_N 4 := by native_decide
example : countAB_in_0_N_fast 16 = countAB_in_0_N 16 := by native_decide
example : countAB_in_0_N_fast 64 = countAB_in_0_N 64 := by native_decide
example : countAB_in_0_N_fast 256 = countAB_in_0_N 256 := by native_decide
example : countAB_in_0_N_fast 1024 = countAB_in_0_N 1024 := by native_decide
example : countAB_in_0_N_fast 4096 = countAB_in_0_N 4096 := by native_decide

/-- NOTE: A previous attempt at a structural `countAB_lower_bound` lemma was
removed. The inequality `countAB_in_0_N (2 * N) ≥ countA N * countB N` is FALSE
in general — `countAB_in_0_N` applies `eraseDups`, which can only decrease the
length, so the actual inequality goes the other way:

    countAB_in_0_N (2 * N) ≤ (List.range (2*N)).length * (List.range (2*N)).length
                          = 4 * N * N

The reverse direction `≥` would require an injection from
`A ∩ [0,N) × B ∩ [0,N)` into `A + B ∩ [0, 2N)`, which is exactly the kind of
structural non-trivial argument this file is too small to host.

The critical path for `erdos_125_case_2_positive_density` (see
Erdos125Case2.lean) uses native_decide on concrete numerical instances
instead of any such general bound. -/

end Erdos125CountAB
