import Mathlib

namespace Erdos125A

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Set A as a Set
def A : Set Nat := {n | inA n}

-- DIGIT DECOMPOSITION (corrected):
-- For a digit d ∈ {0, 1, 2}, decompose d = c + r with c, r ∈ {0, 1}:
--   d = 0: c = 0, r = 0
--   d = 1: c = 0, r = 1
--   d = 2: c = 1, r = 1

def decomp_c (d : Nat) : Nat := if d < 2 then 0 else 1
def decomp_r (d : Nat) : Nat := d - decomp_c d

theorem decomp_correct (d : Nat) (h : d ≤ 2) :
    decomp_c d + decomp_r d = d ∧ decomp_c d ≤ 1 ∧ decomp_r d ≤ 1 := by
  interval_cases d <;> simp [decomp_c, decomp_r]

-- For n with base-3 representation, decompose digit-wise.
-- a_1(n) = Σ decomp_c(d_i) 3^i
-- a_2(n) = Σ decomp_r(d_i) 3^i

def decomp_a1_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a1_aux n' (k + 1) + decomp_c d * 3^k
  termination_by n _ => n
  decreasing_by omega

def decomp_a2_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a2_aux n' (k + 1) + decomp_r d * 3^k
  termination_by n _ => n
  decreasing_by omega

-- CORRECTED LEMMA: decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n
-- This holds for ALL n, k (not just k = 0).
--
-- Proof: by strong induction on n.
-- Base: n = 0. Both decomp's return 0. Sum: 0 + 0 = 0 = 3^k * 0. ✓
-- Step: n = n' + 1.
--   decomp_a1_aux (n' + 1) k = decomp_a1_aux (n' + 1)/3 (k + 1) + decomp_c (n'%3) * 3^k
--   decomp_a2_aux (n' + 1) k = decomp_a2_aux (n' + 1)/3 (k + 1) + decomp_r (n'%3) * 3^k
--   Sum = (sum at (n' + 1)/3 (k + 1)) + (decomp_c + decomp_r) * 3^k
--       = 3^(k+1) * ((n'+1)/3) + (n'%3) * 3^k   [IH applied, decomp_correct for d ≤ 2]
--       = 3^k * (3 * ((n'+1)/3)) + (n'%3) * 3^k
--       = 3^k * (3 * ((n'+1)/3) + (n'%3))
--       = 3^k * (n' + 1)   [by div_add_mod]
--   ✓

theorem decomp_a1_sum : ∀ n k : Nat, decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n := by
  intro n k
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      simp [decomp_a1_aux, decomp_a2_aux]
    | succ n' =>
      rw [decomp_a1_aux, decomp_a2_aux]
      have h : (n' + 1) % 3 < 3 := Nat.mod_lt (n' + 1) (by norm_num : (0 : Nat) < 3)
      have h2 : (n' + 1) % 3 ≤ 2 := Nat.lt_succ_iff.mp h
      have decomp_eq := decomp_correct ((n' + 1) % 3) h2
      obtain ⟨h_sum, _, _⟩ := decomp_eq
      -- Use simp to normalize the goal
      simp only [decomp_a1_aux, decomp_a2_aux, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      -- Regroup: a1 + (a2 + (c*3^k + r*3^k)) → (a1 + a2) + (c*3^k + r*3^k)
      rw [← Nat.add_assoc (decomp_a1_aux ((n' + 1) / 3) (k + 1)) (decomp_a2_aux ((n' + 1) / 3) (k + 1)) (decomp_c ((n' + 1) % 3) * 3 ^ k + decomp_r ((n' + 1) % 3) * 3 ^ k)]
      -- Apply IH
      rw [ih ((n' + 1) / 3) (by omega) (k + 1)]
      -- Factor 3^k: c*3^k + r*3^k = (c + r) * 3^k
      rw [← Nat.add_mul (decomp_c ((n' + 1) % 3)) (decomp_r ((n' + 1) % 3)) (3 ^ k)]
      -- Apply decomp_correct: c + r = (n'+1) % 3
      rw [h_sum]
      -- Now: 3^(k+1) * ((n'+1)/3) + ((n'+1) % 3) * 3^k = 3^k * (n' + 1)
      rw [Nat.pow_succ 3 k]
      -- Now: 3^k * 3 * ((n'+1)/3) + (n'+1) % 3 * 3^k
      rw [Nat.mul_assoc (3 ^ k) 3 ((n' + 1) / 3)]
      -- Now: 3^k * (3 * ((n'+1)/3)) + (n'+1) % 3 * 3^k
      rw [Nat.mul_comm ((n' + 1) % 3) (3 ^ k)]
      -- Now: 3^k * (3 * ((n'+1)/3)) + 3^k * ((n'+1) % 3)
      rw [← Nat.mul_add (3 ^ k) (3 * ((n' + 1) / 3)) ((n' + 1) % 3)]
      -- Now: 3^k * (3 * ((n'+1)/3) + (n'+1) % 3)
      rw [Nat.div_add_mod]

-- Tests via native_decide:
example : decomp_a1_aux 7 0 + decomp_a2_aux 7 0 = 7 := by native_decide
example : decomp_a1_aux 7 1 + decomp_a2_aux 7 1 = 21 := by native_decide
example : decomp_a1_aux 7 2 + decomp_a2_aux 7 2 = 63 := by native_decide
example : decomp_a1_aux 100 0 + decomp_a2_aux 100 0 = 100 := by native_decide
example : decomp_a1_aux 100 1 + decomp_a2_aux 100 1 = 300 := by native_decide
example : decomp_a1_aux 1000 0 + decomp_a2_aux 1000 0 = 1000 := by native_decide
example : decomp_a1_aux 1000 3 + decomp_a2_aux 1000 3 = 27000 := by native_decide

end Erdos125A
