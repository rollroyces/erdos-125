import Mathlib
namespace Erdos125A
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

example (n' : Nat) (h : inA n' = true) : inA (3 * (n' + 1)) = true := by
  -- Use induction on n' first to break into base case.
  induction n' using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      -- inA (3 * 1) = inA 3.
      -- Apply inA.eq_2 to n = 2: inA 3 = if 3 % 3 < 2 then inA (3 / 3) else false
      --                     = if 0 < 2 then inA 1 else false = true (need inA 1 = true).
      -- Apply inA.eq_2 to n = 0: inA 1 = if 1 % 3 < 2 then inA (1 / 3) else false = inA 0 = true.
      simp [inA]
    | n' + 1 =>
      -- Goal: inA (3 * (n' + 1 + 1)) = inA (3 * n' + 6) = true.
      -- This isn't simpler. Let me use inA.eq_2:
      rw [inA.eq_2]
      -- Goal: (if (3 * (n' + 1 + 1)) % 3 < 2 then inA ((3 * (n' + 1 + 1)) / 3) else false) = true.
      have hmod : (3 * (n' + 1 + 1)) % 3 = 0 := by omega
      have hdiv : (3 * (n' + 1 + 1)) / 3 = n' + 1 + 1 := by omega
      rw [hmod, hdiv]
      -- Goal: inA (n' + 1 + 1) = inA n = true = h
      exact h
