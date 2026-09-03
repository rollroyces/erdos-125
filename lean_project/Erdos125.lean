import Mathlib

namespace Erdos125

def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

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
      rw [Nat.mul_mod_right]
    have h_div : (3 * k + 2 + 1) / 3 = k + 1 := by
      rw [show (3 * k + 2 + 1) = 3 * (k + 1) from by ring]
      exact Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 2)
    rw [h_mod, h_div]
    have h_lt : (0 : Nat) < 2 := by norm_num
    rw [if_pos h_lt]

-- "Lowest digit 2" lemma: inA (3 * m + 2) = false
theorem inA_3m_2_eq_false : ∀ m : Nat, inA (3 * m + 2) = false := by
  intro m
  have h_eq : 3 * m + 2 = 3 * m + 1 + 1 := by ring
  rw [h_eq, inA]
  have h_mod : (3 * m + 1 + 1) % 3 = 2 := by omega
  rw [h_mod]
  have h_neg : ¬ (2 < 2) := by omega
  simp [h_neg]

example : inA 2 = false := inA_3m_2_eq_false 0
example : inA 5 = false := inA_3m_2_eq_false 1
example : inA 8 = false := inA_3m_2_eq_false 2

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide

end Erdos125