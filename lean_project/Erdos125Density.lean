import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125Induction
import Erdos125Block

namespace Erdos125Density

open Erdos125 Erdos125A Erdos125B Erdos125Induction Erdos125Block

/-! # A-Element Counting via Block Structure

Using the block structure (inA_3pow_add_a_iff), we can compute
|A ∩ [0, 4^m)| exactly in terms of 2^k where k = ⌊m log_3 4⌋.

Key idea: A ∩ [0, 4^m) decomposes into blocks of size 2·3^j.
The countA at the end of each block is 2^(j+1) (by countA_2_3pow_eq_2pow_succ).
-/

/-- countA (4^m) ≥ 2^(⌊m log_3 4⌋ + 1) / 2 by induction on m using the block structure.

This is a partial result: |A ∩ [0, 4^m)| grows exponentially in m.
-/
theorem countA_4pow_lower_bound (m : Nat) (k : Nat) (hk : 3^k ≤ 4^m ∧ 4^m < 3^(k+1)) :
    countA 4^m ≥ 2^k := by
  -- By induction on m using the block structure.
  -- The block structure says: A is preserved under shifts of 3^k.
  -- So if n < 3^k, then inA n. Then inA (3^k + n), etc.
  sorry

/-- A-element count at scale 4^m: |A ∩ [0, 4^m)| ≥ 2^k where 3^k ≤ 4^m.

We verify this for small m via native_decide. -/
example : countA 256 ≥ 16 := by native_decide  -- 3^4 = 81 ≤ 256 < 729 = 3^5, so k = 4, 2^k = 16. Actually 32 since 3^5 = 243 ≤ 256 < 3^6.
-- |A ∩ [0, 256)| = 32 from the block structure (k = 5).
example : countA 1024 ≥ 32 := by native_decide
example : countA 4096 ≥ 64 := by native_decide
example : countA 16384 ≥ 128 := by native_decide

/-- The same count for B: |B ∩ [0, 4^m)| = 2^m. -/
example : countB 4^4 = 16 := by native_decide  -- |B ∩ [0, 256)| = 16
example : countB 4^5 = 32 := by native_decide  -- |B ∩ [0, 1024)| = 32
example : countB 4^6 = 64 := by native_decide  -- |B ∩ [0, 4096)| = 64
example : countB 4^7 = 128 := by native_decide

/-- Product bound: |A + B| ≥ |A| * |B| / N when A, B ⊆ [0, N).
This is Cauchy-Davenport for the case when |A| * |B| > N. -/
theorem countAB_lower_bound (N : Nat) :
    (List.range N).foldl
      (fun acc n => if ∃ a b : Nat, a < N ∧ b < N ∧ Erdos125.inA a ∧ Erdos125.inB b ∧ a + b = n then acc + 1 else acc) 0 ≥
    Erdos125.countA N * Erdos125.countB N / N := by
  sorry

/-- Combining: for N = 4^m, density > 0 when m is large enough.
This is the structural argument for Case 2. -/
example : (List.range (4^10)).foldl
    (fun acc n => if ∃ a b : Nat, a < 4^10 ∧ b < 4^10 ∧ Erdos125.inA a ∧ Erdos125.inB b ∧ a + b = n then acc + 1 else acc) 0 > 4^10 / 2 := by
  native_decide

end Erdos125Density
