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

-- KEY LEMMA: inA (3 * n) = inA n for all n
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
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

-- B: integers with only digits 0, 1 in base 4
def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

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

-- countA_in_range: |A ∩ [lo, hi)| (with lo ≤ hi)
def countA_in_range (lo hi : Nat) : Nat :=
  ((List.range hi).filter (fun n => n ≥ lo && inA n)).length

-- countB_in_range: |B ∩ [lo, hi)|
def countB_in_range (lo hi : Nat) : Nat :=
  ((List.range hi).filter (fun n => n ≥ lo && inB n)).length

-- THE MAIN THEOREM: countA (3^k) = 2^k for all k
--
-- Proof by strong induction on k.
-- For k = 0: countA 1 = 1 = 2^0.
-- For k → k+1: split [0, 3^(k+1)) into:
--   [0, 3^k): by IH, count = 2^k
--   [3^k, 2·3^k): n = 3^k + r, r in [0, 3^k). inA n ↔ inA r (by inA_3n_eq_n)
--                   so count = 2^k
--   [2·3^k, 3^(k+1)): leading digit is 2, so inA n = false. count = 0
-- Total: 2^k + 2^k + 0 = 2^(k+1)
--
-- The base case and inductive step need the range decomposition.
-- Below, we use the fact that list operations work for our purposes.

theorem countA_3pow_eq_2pow : ∀ k : Nat, countA (3^k) = 2^k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    cases k with
    | zero =>
      -- 3^0 = 1, countA 1 = 1, 2^0 = 1.
      native_decide
    | succ k' =>
      -- We need to show countA (3^(k'+1)) = 2^(k'+1).
      -- 3^(k'+1) = 3 * 3^k'
      -- countA (3 * 3^k') = (size of A in [0, 3 * 3^k'))
      --                       = (size in [0, 3^k')) + (size in [3^k', 2*3^k')) + (size in [2*3^k', 3^(k'+1)))
      --                       = 2^k' + 2^k' + 0
      --                       = 2^(k'+1)
      sorry  -- requires proving the range decomposition

-- Tests of the bijection
example : inA 3 = inA 1 := inA_3n_eq_n 1
example : inA 9 = inA 3 := inA_3n_eq_n 3
example : inA 27 = inA 9 := inA_3n_eq_n 9

-- Tests of the main theorem (via native_decide)
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide

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