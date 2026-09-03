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
-- 
-- Equivalently: c = (d + 1) / 2 (i.e., 0 if d ≤ 1, 1 if d = 2) ... no wait.
--   d = 0: (0+1)/2 = 0. ✓
--   d = 1: (1+1)/2 = 1. ✗ (we want c = 0)
--   d = 2: (2+1)/2 = 1. ✓
-- 
-- So (d + 1) / 2 doesn't work. Use:
-- c = if d < 2 then 0 else 1
-- r = d - c

def decomp_c (d : Nat) : Nat := if d < 2 then 0 else 1
def decomp_r (d : Nat) : Nat := d - decomp_c d

theorem decomp_correct (d : Nat) (h : d ≤ 2) :
    decomp_c d + decomp_r d = d ∧ decomp_c d ≤ 1 ∧ decomp_r d ≤ 1 := by
  interval_cases d <;> simp [decomp_c, decomp_r]

-- For n with base-3 representation, decompose digit-wise.
-- a_1(n) = Σ decomp_c(d_i) * 3^i
-- a_2(n) = Σ decomp_r(d_i) * 3^i

-- Recursive definitions. Process digits from low to high.

def decomp_a1_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a1_aux n' (k + 1) + decomp_c d * 3^k
  termination_by n _ => n
  decreasing_by sorry

def decomp_a2_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a2_aux n' (k + 1) + decomp_r d * 3^k
  termination_by n _ => n
  decreasing_by sorry

-- For n > 0: decomp_a1_aux n 0 and decomp_a2_aux n 0 are the decompositions.
-- 
-- Theorem: decomp_a1_aux n 0 + decomp_a2_aux n 0 = n.
-- 
-- Proof: by induction on n.

theorem decomp_a1_sum : ∀ n k : Nat, decomp_a1_aux n k + decomp_a2_aux n k = n := by
  intro n k
  -- Use strong induction on n.
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      simp [decomp_a1_aux, decomp_a2_aux]
    | succ n' =>
      have h : (n' + 1) % 3 < 3 := Nat.mod_lt (n' + 1) (by norm_num : (0 : Nat) < 3)
      have h2 : (n' + 1) % 3 ≤ 2 := Nat.lt_succ_iff.mp h
      have decomp_eq := decomp_correct ((n' + 1) % 3) h2
      obtain ⟨h_sum, _, _⟩ := decomp_eq
      have eq_a1 : decomp_a1_aux (n' + 1) k = decomp_a1_aux ((n' + 1) / 3) (k + 1) + decomp_c ((n' + 1) % 3) * 3^k := by
        rw [decomp_a1_aux]
      have eq_a2 : decomp_a2_aux (n' + 1) k = decomp_a2_aux ((n' + 1) / 3) (k + 1) + decomp_r ((n' + 1) % 3) * 3^k := by
        rw [decomp_a2_aux]
      rw [eq_a1, eq_a2]
      -- The IH gives: decomp_a1_aux ((n'+1)/3) (k+1) + decomp_a2_aux ((n'+1)/3) (k+1) = (n'+1)/3
      -- The goal is: decomp_a1 ((n'+1)/3) (k+1) + decomp_c ((n'+1)%3) * 3^k + 
      --              (decomp_a2 ((n'+1)/3) (k+1) + decomp_r ((n'+1)%3) * 3^k) = n'+1
      -- 
      -- Approach: replace decomp_a1 with the sum, then use IH.
      -- Actually, the IH gives an equality involving decomp_a1 + decomp_a2 = (n'+1)/3.
      -- We want to show (a1 + c*3^k) + (a2 + r*3^k) = (a1 + a2) + (c+r)*3^k = (n'+1)/3 + ((n'+1) % 3).
      -- 
      -- Strategy: rewrite the goal to (a1 + a2) + (c*3^k + r*3^k) = n' + 1.
      -- Then use IH to replace (a1 + a2) with (n'+1)/3.
      -- Then goal becomes (n'+1)/3 + ((n'+1) % 3) = n' + 1.
      -- This is Nat.div_add_mod.
      -- 
      -- To rewrite the LHS to a1 + a2 + (c*3^k + r*3^k):
      -- Goal: a1 + (c*3^k + (a2 + r*3^k))
      -- Use omega on the unfolded goal.
      rw [ih ((n' + 1) / 3) (by omega) (k + 1)]
      rw [← Nat.mul_add_one (decomp_c ((n' + 1) % 3)) (decomp_r ((n' + 1) % 3)) 3^k]
      rw [h_sum]
      -- Now: (n'+1)/3 + ((n'+1) % 3) * 3^k = n' + 1
      -- This is div_add_mod but we have an extra 3^k.
      -- Wait, (n'+1) % 3 < 3, so ((n'+1) % 3) * 3^k is huge. So the equality can't hold directly.
      -- 
      -- I think I have a bug. Let me reconsider.
      sorry

example : decomp_a1_aux 7 0 + decomp_a2_aux 7 0 = 7 := by
  -- Should hold by decomp_a1_sum
  exact decomp_a1_sum 7 0

-- Verify both decompositions are in A:
-- For decomp_a1 n 0 to be in A, all its base-3 digits must be 0/1.
-- Digit at position k of decomp_a1 n 0 = decomp_c ((n / 3^k) % 3) = 0 or 1.
-- So all digits are 0/1, hence in A.

-- Lemma: for any n, inA (decomp_a1_aux n 0) = true.
-- Proof: by induction on n, showing each digit is 0/1.

theorem inA_decomp_a1 : ∀ n k : Nat, inA (decomp_a1_aux n k) = true := by
  intro n k
  induction n using Nat.rec with
  | zero =>
    simp [decomp_a1_aux, inA]
  | succ n' ih =>
    -- decomp_a1_aux (n' + 1) k = decomp_a1_aux ((n'+1)/3) (k+1) + decomp_c((n'+1)%3) * 3^k
    -- decomp_c gives 0 or 1, so the addition preserves A-membership (since A is closed under + 3^k for elements in A).
    -- 
    -- Hmm this needs more work. Let me use a helper lemma.
    sorry

-- Tests via native_decide:
example : decomp_a1_aux 7 0 + decomp_a2_aux 7 0 = 7 := by native_decide
example : decomp_a1_aux 100 0 + decomp_a2_aux 100 0 = 100 := by native_decide
example : decomp_a1_aux 1000 0 + decomp_a2_aux 1000 0 = 1000 := by native_decide

example : inA (decomp_a1_aux 7 0) = true := by native_decide
example : inA (decomp_a2_aux 7 0) = true := by native_decide
example : inA (decomp_a1_aux 100 0) = true := by native_decide
example : inA (decomp_a2_aux 100 0) = true := by native_decide
example : inA (decomp_a1_aux 1000 0) = true := by native_decide
example : inA (decomp_a2_aux 1000 0) = true := by native_decide

end Erdos125A
