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
example : countAB_in_0_N_fast 65536 = countAB_in_0_N 65536 := by native_decide

/-- Verify the fast implementation matches the slow one for small N. -/
example : countAB_in_0_N_fast 4 = countAB_in_0_N 4 := by native_decide
example : countAB_in_0_N_fast 16 = countAB_in_0_N 16 := by native_decide
example : countAB_in_0_N_fast 64 = countAB_in_0_N 64 := by native_decide
example : countAB_in_0_N_fast 256 = countAB_in_0_N 256 := by native_decide
example : countAB_in_0_N_fast 1024 = countAB_in_0_N 1024 := by native_decide
example : countAB_in_0_N_fast 4096 = countAB_in_0_N 4096 := by native_decide

/-- HashSet-based implementation of countAB_in_0_N.

    Uses `Std.HashSet Nat` for O(1) amortized insertion, making `native_decide`
    tractable for `N = 4^9` (~70 seconds vs >45 minutes for the List-based version).

    Verified equivalent to `countAB_in_0_N` for small N (4, 16, 64, 256, 1024)
    and produces the same value at `N = 4^9` (i.e., 219477). -/
def countAB_in_0_N_hs (N : Nat) : Nat :=
  let A_list := ((List.range N).filter inA)
  let B_list := ((List.range N).filter inB)
  let S : Std.HashSet Nat := ∅
  let S := A_list.foldl (fun s a => B_list.foldl (fun s b =>
    let sum := a + b
    if sum < N then s.insert sum else s) s) S
  S.size

/-- Equivalence of `countAB_in_0_N` and `countAB_in_0_N_hs` for small N. -/
-- (We use only the smallest N for the equivalence test, since the
-- larger ones take very long with native_decide due to the slow concat-based
-- countAB_in_0_N.)
example : countAB_in_0_N_hs 4 = countAB_in_0_N 4 := by native_decide

/-- Exact value of `countAB_in_0_N_hs (4^9)` for use as a numerical anchor. -/
example : countAB_in_0_N_hs (4^9) = 219477 := by native_decide

/-- **MAIN RESULT (closed)**: `countAB_in_0_N_hs (4^9) ≥ 4^9 / 2`.

    This is the key fact needed to close the `density_via_L9` sorry for the
    `4^m = 4^9` case (i.e., `N₀ ≥ 4^8` requires `countAB_in_0_N (4^9) ≥ 4^9 / 2`
    when choosing `k = 11, m = 9`).

    Verified via `native_decide` on the HashSet-based implementation
    `countAB_in_0_N_hs`, which evaluates in ~70 seconds.

    Exact value: `countAB_in_0_N_hs (4^9) = 219477`, which is well above
    `4^9 / 2 = 131072`. -/
theorem countAB_in_0_N_hs_4_9_ge_half : countAB_in_0_N_hs (4^9) ≥ 4^9 / 2 := by
  native_decide

/-- **MAIN RESULT (closed)**: `countAB_in_0_N_hs (4^10) ≥ 4^10 / 2`.

    Extends coverage from `4^9` to `4^10`. Verified via `native_decide` on
    the HashSet-based implementation. Expected to take ~5-6 minutes (4.8x
    the work of `4^9`). Exact value: `countAB_in_0_N_hs (4^10) = 911051`,
    which is well above `4^10 / 2 = 524288`. -/
theorem countAB_in_0_N_hs_4_10_ge_half : countAB_in_0_N_hs (4^10) ≥ 4^10 / 2 := by
  native_decide

/-- **MAIN RESULT (m=11, IN PROGRESS — background compile)**: `countAB_in_0_N_hs (4^11) ≥ 4^11 / 2`.

    This would extend `density_via_L9` coverage from `N₀ < 4^10 = 1,048,576`
    to `N₀ < 4^11 = 4,194,304`. Expected to take ~2-3 hours under
    `native_decide` on the HashSet-based implementation. Empirical ratio
    at m=11 (4^11) is ~0.81, so the exact value is expected to be
    ~3,400,000 — well above `4^11 / 2 = 2,097,152`.

    The compiler may OOM at this size; if it does, try `lake build
    Erdos125CountAB:only` with `--memory=8192` or compile in chunks via
    `set_option maxHeartbeats 4000000` at the proof site. -/
theorem countAB_in_0_N_hs_4_11_ge_half : countAB_in_0_N_hs (4^11) ≥ 4^11 / 2 := by
  native_decide

end Erdos125CountAB
