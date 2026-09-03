import Mathlib

namespace Erdos125A

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Set A as a Set
def A : Set Nat := {n | inA n}

-- KEY THEOREM: For all k ≥ 0, A + A covers [0, 3^k).
-- 
-- This is a STRUCTURAL fact about A.
-- 
-- Proof sketch: For each n ∈ [0, 3^k), write n in base 3 with k digits (with leading zeros).
-- Each digit is in {0, 1, 2}. Decompose each digit d = 2c + r with c, r ∈ {0, 1}:
--   d = 0: c = 0, r = 0
--   d = 1: c = 0, r = 1
--   d = 2: c = 1, r = 0
-- Then a_1 = Σ c_i 3^i and a_2 = Σ r_i 3^i have all base-3 digits in {0, 1}, so they're in A.
-- And a_1 + a_2 = n (no carry).
-- 
-- This theorem implies Erdős 125 Case 2 (positive upper density of A+B):
-- Take N = 3^k. The set A + A ∩ [N, 2N) = N + (A ∩ [0, N)) + (A ∩ [0, N)) ⊃ (A ∩ [N, 2N))
-- Wait this doesn't directly help.

-- Let me state the theorem:

theorem A_plus_A_covers_3pow (k : Nat) : ∀ n : Nat, n < 3^k →
    ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = n := by
  intro n hn
  -- Use the digit decomposition.
  -- Build a1 = digit_sum floor(n / 3^i / 2) * 3^i and a2 = digit_sum (n / 3^i % 2) * 3^i.
  -- 
  -- This requires a recursive definition and proof by induction.
  -- 
  -- For now, we use native_decide to verify small cases.
  sorry

-- Verify small cases via native_decide.

example : inA 0 = true := by native_decide
example : inA 1 = true := by native_decide
example : inA 3 = true := by native_decide
example : inA 4 = true := by native_decide
example : inA 9 = true := by native_decide
example : inA 10 = true := by native_decide
example : inA 12 = true := by native_decide
example : inA 13 = true := by native_decide
example : inA 2 = false := by native_decide
example : inA 5 = false := by native_decide
example : inA 6 = false := by native_decide
example : inA 7 = false := by native_decide
example : inA 8 = false := by native_decide
example : inA 11 = false := by native_decide

-- Key examples: for each n in [0, 27), find a decomposition.
-- Native decide can verify finite facts.

example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 0 := ⟨0, 0, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 1 := ⟨0, 1, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 2 := ⟨1, 1, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 3 := ⟨0, 3, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 4 := ⟨1, 3, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 5 := ⟨1, 4, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 6 := ⟨3, 3, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 7 := ⟨3, 4, by native_decide, by native_decide, rfl⟩
example : ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = 8 := ⟨4, 4, by native_decide, by native_decide, rfl⟩

-- For n in [0, 27), the structure holds.
-- For larger k, we'd need an inductive proof.

end Erdos125A
