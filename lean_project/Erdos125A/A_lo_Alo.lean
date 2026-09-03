import Mathlib

namespace Erdos125A

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- Set A as a Set
def A : Set Nat := {n | inA n}

-- Helper: for any digit d ∈ {0, 1, 2}, we have d = 2 * (d / 2) + d % 2.
-- By cases: 0 = 2*0+0, 1 = 2*0+1, 2 = 2*1+0.

theorem digit_decomp (d : Nat) (h : d ≤ 2) : d = 2 * (d / 2) + d % 2 := by
  rcases d with (_ | _ | _ | _) <;> simp_all

-- For n < 3^k, write n in base 3 with k digits (leading zeros allowed).
-- Each digit d_i ∈ {0, 1, 2}. Decompose d_i = 2 * c_i + r_i with c_i, r_i ∈ {0, 1}.
-- Then a_1 = Σ c_i 3^i, a_2 = Σ r_i 3^i are in A, and a_1 + a_2 = n.
-- 
-- Define the recursive decomposition.

def decompA1 : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k + 1 => -- process one digit
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    let rest := decompA1 n' k
    if d < 2 then rest else rest + 3^k
  termination_by _ n k => (k + 1, n + 1)
  -- This needs care. Let me redo.

-- Let me think differently. Define a function that, given n and k, computes a_1, a_2.

-- Actually, the cleanest is to use `native_decide` for small cases and prove the general case differently.

-- For now, let me just verify the digit decomposition works for small n.

example : (0 : Nat) = 0 := rfl
example : (1 : Nat) = 1 := rfl
example : (2 : Nat) = 2 := rfl

-- d / 2 for d = 0, 1, 2
example : (0 : Nat) / 2 = 0 := rfl
example : (1 : Nat) / 2 = 0 := rfl
example : (2 : Nat) / 2 = 1 := rfl

-- d % 2 for d = 0, 1, 2
example : (0 : Nat) % 2 = 0 := rfl
example : (1 : Nat) % 2 = 1 := rfl
example : (2 : Nat) % 2 = 0 := rfl

-- So:
-- d=0: a1=0, a2=0
-- d=1: a1=0, a2=1
-- d=2: a1=1, a2=0

-- For multi-digit n, we apply this digit-wise.
-- 
-- For example, n = 5 in base 3 = 12_3. Digits: 1, 2.
-- a_1: (0, 1) → 0 + 1*3 = 3
-- a_2: (1, 0) → 1 + 0*3 = 1
-- Check: 3 + 1 = 5. ✓
-- And 3 = 10_3 (digits 0/1). 1 = 1_3 (digit 0/1). ✓

-- For n = 8 = 22_3: a_1 = 11_3 = 4, a_2 = 11_3 = 4. 4 + 4 = 8. ✓

-- For n = 27 = 1000_3: a_1 = 1000_3 = 27, a_2 = 0. 27 + 0 = 27. ✓

-- Let me define the decomp properly.

-- For n ∈ [0, 3^k), define a_1(n, k) and a_2(n, k).
-- 
-- Recursively: a_i(n, k) = a_i(n / 3, k - 1) + 3^(k-1) * c_i where c_i depends on n % 3.

def decompA1Aux : Nat → Nat → Nat
  | n, 0 => 0
  | n, k + 1 =>
    let d := n % 3
    let n' := n / 3
    let rest := decompA1Aux n' k
    if d < 2 then rest else rest + 3^k
  termination_by _ n k => k
  decreasing_by sorry

-- This is getting complex. Let me just prove the key lemma directly.

-- KEY LEMMA: For any n : Nat with n < 3^k, there exist a_1 a_2 : Nat with:
--   - inA a_1 = true
--   - inA a_2 = true
--   - a_1 + a_2 = n

-- I'll prove this by strong induction on k.
-- 
-- For k = 0: n = 0. a_1 = 0, a_2 = 0. Both in A (inA 0 = true). 0 + 0 = 0. ✓
-- 
-- For k + 1: Let n < 3^(k+1). Write n = 3q + d with d ∈ {0, 1, 2}.
-- By IH, q < 3^k (since q = n / 3 < 3^(k+1) / 3 = 3^k).
-- So there exist a_1', a_2' ∈ A with a_1' + a_2' = q.
-- 
-- Now construct a_1 = a_1' + c_1 * 3^k, a_2 = a_2' + c_2 * 3^k where:
-- - d = 0: c_1 = 0, c_2 = 0
-- - d = 1: c_1 = 0, c_2 = 1
-- - d = 2: c_1 = 1, c_2 = 0
-- 
-- Then a_1 + a_2 = a_1' + a_2' + (c_1 + c_2) * 3^k = q + d = n.
-- And a_1, a_2 have base-3 representation: digits from a_i', plus c_i at position k.
-- Since a_i' has digits 0/1 and c_i ∈ {0, 1}, a_i has digits 0/1. So a_i ∈ A.

theorem decomp_inA (n k : Nat) (hn : n < 3^k) :
    ∃ a1 a2 : Nat, inA a1 = true ∧ inA a2 = true ∧ a1 + a2 = n := by
  induction k using Nat.rec with
  | zero =>
    -- n < 1, so n = 0.
    have : n = 0 := by have := hn; omega
    subst this
    exact ⟨0, 0, rfl, rfl, rfl⟩
  | succ k ih =>
    -- n < 3^(k+1), so n = 3 * (n/3) + (n % 3) with n/3 < 3^k.
    set q := n / 3
    set d := n % 3
    have hq : q < 3^k := by
      rw [Nat.lt_div_iff_mul_lt 3]
      · omega
      · exact Nat.zero_lt_succ 0
    have hd : d < 3 := Nat.mod_lt n (by norm_num : (0 : Nat) < 3)
    -- Decompose d ∈ {0, 1, 2}.
    -- By IH, q = a_1' + a_2' with a_1', a_2' ∈ A.
    obtain ⟨a1', a2', ha1', ha2', hsum'⟩ := ih q hq
    -- Construct a_1, a_2.
    -- a_1 = a_1' + c_1 * 3^k where c_1 = d / 2
    -- a_2 = a_2' + c_2 * 3^k where c_2 = d % 2
    set c1 := d / 2
    set c2 := d % 2
    have h_decomp : d = 2 * c1 + c2 := by
      rw [Nat.div_add_mod]
    -- Need to show: c1 ≤ 1 and c2 ≤ 1.
    have hc1 : c1 ≤ 1 := by
      rcases d with (_ | _ | _ | _) <;> simp_all
    have hc2 : c2 ≤ 1 := by
      rcases d with (_ | _ | _ | _) <;> simp_all
    set a1 := a1' + c1 * 3^k
    set a2 := a2' + c2 * 3^k
    -- Need: inA a1 = true and inA a2 = true.
    -- a1 in A: a1 has base-3 representation = (a1')'s digits + c1 at position k.
    -- a1' has digits 0/1. c1 ∈ {0, 1}. So a1 has digits 0/1 in [0, 3^k) ∪ {position k}.
    -- Therefore a1 ∈ A.
    -- 
    -- For Lean: use the equation lemma for inA.
    have ha1 : inA a1 = true := by
      -- Unfold inA.
      sorry  -- This requires proving the unfolding lemma for inA
    have ha2 : inA a2 = true := by sorry
    -- a1 + a2 = a1' + a2' + (c1 + c2) * 3^k = q + d = n
    have hsum : a1 + a2 = n := by
      dsimp [a1, a2, c1, c2]
      rw [hsum']
      rw [h_decomp]
      rw [Nat.div_add_mod]
    exact ⟨a1, a2, ha1, ha2, hsum⟩

end Erdos125A