import Mathlib

namespace Erdos125B

-- B: integers with only digits 0, 1 in base 4
def inB : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 4 < 2 then inB ((n + 1) / 4) else false
termination_by n => n

-- DIGIT DECOMPOSITION for B + B + B = [0, 4^m):
-- For a digit d ∈ {0, 1, 2, 3}, decompose d = c + r + s with c, r, s ∈ {0, 1}:
--   d = 0: c = 0, r = 0, s = 0
--   d = 1: c = 1, r = 0, s = 0
--   d = 2: c = 1, r = 1, s = 0
--   d = 3: c = 1, r = 1, s = 1

def decomp_b_c (d : Nat) : Nat := if d ≥ 1 then 1 else 0
def decomp_b_r (d : Nat) : Nat := if d ≥ 2 then 1 else 0
def decomp_b_s (d : Nat) : Nat := if d ≥ 3 then 1 else 0

theorem decomp_b_correct (d : Nat) (h : d ≤ 3) :
    decomp_b_c d + decomp_b_r d + decomp_b_s d = d
    ∧ decomp_b_c d ≤ 1 ∧ decomp_b_r d ≤ 1 ∧ decomp_b_s d ≤ 1 := by
  rcases d with (_ | _ | _ | _ | _) <;> simp [decomp_b_c, decomp_b_r, decomp_b_s] <;> omega

-- Define the decomposition function for B + B + B.
def decomp_b1_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 4
    let n' := (n + 1) / 4
    decomp_b1_aux n' (k + 1) + decomp_b_c d * 4^k
  termination_by n _ => n
  decreasing_by omega

def decomp_b2_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 4
    let n' := (n + 1) / 4
    decomp_b2_aux n' (k + 1) + decomp_b_r d * 4^k
  termination_by n _ => n
  decreasing_by omega

def decomp_b3_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 4
    let n' := (n + 1) / 4
    decomp_b3_aux n' (k + 1) + decomp_b_s d * 4^k
  termination_by n _ => n
  decreasing_by omega

-- THEOREM: decomp_b1_aux n k + decomp_b2_aux n k + decomp_b3_aux n k = 4^k * n
-- This holds for ALL n, k.
-- 
-- Proof: by strong induction on n.
-- Base: n = 0. All decomp's return 0. Sum: 0 + 0 + 0 = 0 = 4^k * 0. ✓
-- Step: n = n' + 1.
--   Each decomp_b? aux (n' + 1) k = decomp_b? aux (n' + 1)/4 (k + 1) + d_part * 4^k
--   Sum = (sum at (n'+1)/4 (k+1)) + (c+r+s) * 4^k
--       = 3 * 4^(k+1) * (n'+1)/4 + (n'+1) % 3 * 4^k   [wait, this is for A+A=A]

-- Actually for B+B+B: sum = 4^(k+1) * (n'+1)/4 + (n'+1) % 4 * 4^k
-- Hmm let me re-think.

-- For n > 0:
-- decomp_b1_aux n k = decomp_b1_aux (n/4) (k+1) + decomp_b_c (n%4) * 4^k
-- Similarly for b2 and b3.
-- Sum = (sum at (n/4) (k+1)) + (c + r + s) * 4^k
--     = 4^(k+1) * (n/4) + (n%4) * 4^k   [by IH at (n/4, k+1)]
--     = 4^k * (4 * (n/4) + n%4)
--     = 4^k * n   [by div_add_mod]
-- ✓

theorem decomp_b_sum : ∀ n k : Nat, decomp_b1_aux n k + decomp_b2_aux n k + decomp_b3_aux n k = 4^k * n := by
  intro n k
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      simp [decomp_b1_aux, decomp_b2_aux, decomp_b3_aux]
    | succ n' =>
      rw [decomp_b1_aux, decomp_b2_aux, decomp_b3_aux]
      have h : (n' + 1) % 4 < 4 := Nat.mod_lt (n' + 1) (by norm_num : (0 : Nat) < 4)
      have h2 : (n' + 1) % 4 ≤ 3 := Nat.lt_succ_iff.mp h
      have decomp_eq := decomp_b_correct ((n' + 1) % 4) h2
      obtain ⟨h_sum, _, _, _⟩ := decomp_eq
      -- Fully flatten the LHS using simp.
      simp only [decomp_b1_aux, decomp_b2_aux, decomp_b3_aux, Nat.add_assoc, Nat.add_left_comm]
      -- After simp, LHS = a1 + (a2 + (a3 + (c*4^k + (r*4^k + s*4^k))))
      -- First regroup: (a1 + a2) + (a3 + (c*4^k + (r*4^k + s*4^k)))
      rw [← Nat.add_assoc (decomp_b1_aux ((n' + 1) / 4) (k + 1)) (decomp_b2_aux ((n' + 1) / 4) (k + 1)) (decomp_b3_aux ((n' + 1) / 4) (k + 1) + (decomp_b_c ((n' + 1) % 4) * 4 ^ k + (decomp_b_r ((n' + 1) % 4) * 4 ^ k + decomp_b_s ((n' + 1) % 4) * 4 ^ k)))]
      -- Second regroup: ((a1 + a2) + a3) + (c*4^k + (r*4^k + s*4^k))
      rw [← Nat.add_assoc (decomp_b1_aux ((n' + 1) / 4) (k + 1) + decomp_b2_aux ((n' + 1) / 4) (k + 1)) (decomp_b3_aux ((n' + 1) / 4) (k + 1)) (decomp_b_c ((n' + 1) % 4) * 4 ^ k + (decomp_b_r ((n' + 1) % 4) * 4 ^ k + decomp_b_s ((n' + 1) % 4) * 4 ^ k))]
      -- Apply IH: ((a1 + a2) + a3) = 4^(k+1) * ((n'+1)/4)
      rw [ih ((n' + 1) / 4) (by omega) (k + 1)]
      -- Now LHS = 4^(k+1) * ((n'+1)/4) + (c*4^k + (r*4^k + s*4^k))
      -- Step 1: r*4^k + s*4^k = (r+s)*4^k (inside parens)
      rw [← Nat.add_mul (decomp_b_r ((n' + 1) % 4)) (decomp_b_s ((n' + 1) % 4)) (4 ^ k)]
      -- Step 2: c*4^k + (r+s)*4^k = (c+r+s)*4^k
      rw [← Nat.add_mul (decomp_b_c ((n' + 1) % 4)) (decomp_b_r ((n' + 1) % 4) + decomp_b_s ((n' + 1) % 4)) (4 ^ k)]
      -- Now LHS = 4^(k+1) * ((n'+1)/4) + (c+r+s)*4^k
      -- Normalize (c + (r + s)) to (c + r + s) form
      simp only [Nat.add_assoc] at *
      rw [h_sum]
      rw [Nat.pow_succ 4 k]
      rw [Nat.mul_assoc (4 ^ k) 4 ((n' + 1) / 4)]
      rw [Nat.mul_comm ((n' + 1) % 4) (4 ^ k)]
      rw [← Nat.mul_add (4 ^ k) (4 * ((n' + 1) / 4)) ((n' + 1) % 4)]
      rw [Nat.div_add_mod]

-- Tests via native_decide:
example : decomp_b1_aux 7 0 + decomp_b2_aux 7 0 + decomp_b3_aux 7 0 = 7 := by native_decide
example : decomp_b1_aux 8 0 + decomp_b2_aux 8 0 + decomp_b3_aux 8 0 = 8 := by native_decide
example : decomp_b1_aux 15 0 + decomp_b2_aux 15 0 + decomp_b3_aux 15 0 = 15 := by native_decide
example : decomp_b1_aux 100 0 + decomp_b2_aux 100 0 + decomp_b3_aux 100 0 = 100 := by native_decide
example : decomp_b1_aux 7 1 + decomp_b2_aux 7 1 + decomp_b3_aux 7 1 = 28 := by native_decide
example : decomp_b1_aux 100 1 + decomp_b2_aux 100 1 + decomp_b3_aux 100 1 = 400 := by native_decide

end Erdos125B
