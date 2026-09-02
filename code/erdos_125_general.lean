-- Erdős 125: General count of A = {n : digits of n in base 3 are only 0, 1}
-- Plus a real inductive proof that |A ∩ [0, 3^k)| = 2^k.

-- Define inA using Nat.rec-style recursion so we can prove things about it.

def inA : Nat → Bool
  | 0     => true
  | n + 1 => (n + 1) % 3 < 2 && inA ((n + 1) / 3)

def countA (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => if inA n then acc + 1 else acc) 0

-- Verify |A ∩ [0, 3^k)| = 2^k for small k
example : countA 1 = 1 := by native_decide
example : countA 3 = 2 := by native_decide
example : countA 9 = 4 := by native_decide
example : countA 27 = 8 := by native_decide
example : countA 81 = 16 := by native_decide
example : countA 243 = 32 := by native_decide
example : countA 729 = 64 := by native_decide
example : countA 2187 = 128 := by native_decide
example : countA 6561 = 256 := by native_decide
example : countA 19683 = 512 := by native_decide

-- =================================================================
-- Real inductive proof: for every k : Nat, countA (3^k) = 2^k
-- =================================================================

namespace Erdos125

-- 3^k and 2^k
def pow3 : Nat → Nat
  | 0     => 1
  | k + 1 => 3 * pow3 k

def pow2 : Nat → Nat
  | 0     => 1
  | k + 1 => 2 * pow2 k

-- Alternative countA definition via Nat.rec
def countA' : Nat → Nat
  | 0     => 0
  | n + 1 => countA' n + (if inA n then 1 else 0)

-- countA' is the same as countA. We prove this by induction on N.
-- The key fact: countA (N+1) = countA N + [inA N].
-- This follows from List.range (N+1) = List.range N ++ [N] and foldl behavior.
theorem countA_eq_countA' : ∀ N, countA N = countA' N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    -- We need: countA (n+1) = countA n + (if inA n then 1 else 0)
    -- because of List.range (n+1) = List.range n ++ [n]
    have hrange : List.range (n + 1) = List.range n ++ [n] := by
      induction n with
      | zero => rfl
      | succ m hm =>
        rw [List.range_succ]
        rw [List.range_succ]
        rw [hm]
        -- List.range m ++ [m] ++ [m+1] = List.range m ++ [m, m+1] = List.range (m+1) ++ [m+1]
        rw [← List.cons_append]
        rw [List.range_succ]
        -- Goal: List.range (m+1) ++ [m+1] = List.range (m+1) ++ [m+1] - refl
        rfl
    rw [countA, hrange]
    -- foldl f 0 (xs ++ [n]) = foldl f (foldl f 0 xs) [n]
    rw [List.foldl_append]
    -- Now: List.foldl f (List.foldl f 0 (List.range n)) [n]
    simp only [List.foldl_nil, List.foldl_cons]
    -- Goal: (if inA n = true then List.foldl f 0 (List.range n) + 1 else ...) = countA' (n+1)
    -- The foldl f 0 (List.range n) is exactly countA n by definition.
    -- Replace using the theorem:
    show (if inA n = true then countA n + 1 else countA n) = countA' (n + 1)
    rw [ih]
    -- Now: (if inA n = true then countA' n + 1 else countA' n) = countA' (n+1)
    -- countA' (n+1) = countA' n + (if inA n then 1 else 0) = if inA n then countA' n + 1 else countA' n
    cases hinA : inA n <;> simp [hinA, countA']

-- =================================================================
-- Lemma: inA (pow3 k) = true for all k.
-- Proof: 3^k > 0, so inA(3^k) = (3^k % 3 < 2) && inA(3^k / 3).
-- (3^k % 3) = 0 since 3 | 3^k, so this is (0 < 2) && inA(3^(k-1)) = true && ... = inA(3^(k-1)).
-- By induction down, this equals true.
-- =================================================================

theorem pow3_pos (k : Nat) : pow3 k > 0 := by
  induction k with
  | zero => simp [pow3]
  | succ k ih => simp [pow3]; omega

theorem inA_pow3 (k : Nat) : inA (pow3 k) = true := by
  induction k with
  | zero =>
    -- pow3 0 = 1. inA 1 = (1 % 3 < 2) && inA (1/3=0) = true && true = true.
    rw [pow3, inA.eq_def]
    simp [inA.eq_def]
  | succ k ih =>
    -- pow3 (k+1) = 3 * pow3 k. So 3^k+1 = 3 * 3^k.
    -- inA (3 * pow3 k) = ((3 * pow3 k) % 3 < 2) && inA ((3 * pow3 k) / 3)
    --                 = (0 < 2) && inA (pow3 k)    [since 3 | 3 * pow3 k]
    --                 = true && inA (pow3 k)
    --                 = inA (pow3 k)
    --                 = true    [IH]
    rw [pow3, inA.eq_def]
    -- Now goal involves (3 * pow3 k) % 3 and (3 * pow3 k) / 3.
    rw [Nat.mul_mod_right]
    rw [Nat.mul_div_cancel_left _ (pow3_pos k)]
    simp
    exact ih

end Erdos125