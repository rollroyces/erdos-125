import Mathlib

namespace Erdos125C

-- A: integers with only digits 0, 1 in base 3
def inA : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 < 2 then inA ((n + 1) / 3) else false
termination_by n => n

-- DIGIT DECOMPOSITION (3-way): every d ∈ {0, 1, 2} can be written as c1 + c2 + c3 with c_i ∈ {0, 1}:
--   d = 0: c1=0, c2=0, c3=0
--   d = 1: c1=1, c2=0, c3=0
--   d = 2: c1=1, c2=1, c3=0

def decomp_a_c1 (d : Nat) : Nat := if d < 1 then 0 else 1
def decomp_a_c2 (d : Nat) : Nat := if d < 2 then 0 else 1
def decomp_a_c3 (d : Nat) : Nat := 0

theorem decomp_a_correct (d : Nat) (h : d ≤ 2) :
    decomp_a_c1 d + decomp_a_c2 d + decomp_a_c3 d = d ∧
    decomp_a_c1 d ≤ 1 ∧ decomp_a_c2 d ≤ 1 ∧ decomp_a_c3 d ≤ 1 := by
  interval_cases d <;> simp [decomp_a_c1, decomp_a_c2, decomp_a_c3]

def decomp_a1_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a1_aux n' (k + 1) + decomp_a_c1 d * 3 ^ k
  termination_by n _ => n
  decreasing_by omega

def decomp_a2_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a2_aux n' (k + 1) + decomp_a_c2 d * 3 ^ k
  termination_by n _ => n
  decreasing_by omega

def decomp_a3_aux : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let d := (n + 1) % 3
    let n' := (n + 1) / 3
    decomp_a3_aux n' (k + 1) + decomp_a_c3 d * 3 ^ k
  termination_by n _ => n
  decreasing_by omega

-- MAIN THEOREM: A + A + A = [0, 3^k)
-- Equivalent: for every n < 3^k, there exist a1, a2, a3 ∈ A with a1 + a2 + a3 = n.
-- Proof: digit decomposition gives a1 = Σ c1(d_i) * 3^i, a2 = Σ c2(d_i) * 3^i, a3 = Σ c3(d_i) * 3^i.
-- Then a1 + a2 + a3 = Σ (c1 + c2 + c3)(d_i) * 3^i = Σ d_i * 3^i = n.
-- Since c_i(d) ∈ {0, 1}, each a_i has only digits 0, 1 in base 3, hence a_i ∈ A.
--
-- Lean formalization: prove decomp_a1_aux n k + decomp_a2_aux n k + decomp_a3_aux n k = 3^k * n.
-- (Because a1 + a2 + a3 = n when k=0; the k factor is for shifting.)

theorem decomp_a_sum : ∀ n k : Nat, decomp_a1_aux n k + decomp_a2_aux n k + decomp_a3_aux n k = 3 ^ k * n := by
  intro n k
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      simp [decomp_a1_aux, decomp_a2_aux, decomp_a3_aux]
    | succ n' =>
      rw [decomp_a1_aux, decomp_a2_aux, decomp_a3_aux]
      have h : (n' + 1) % 3 < 3 := Nat.mod_lt (n' + 1) (by norm_num : (0 : Nat) < 3)
      have h2 : (n' + 1) % 3 ≤ 2 := Nat.lt_succ_iff.mp h
      have decomp_eq := decomp_a_correct ((n' + 1) % 3) h2
      obtain ⟨h_sum, _, _, _⟩ := decomp_eq
      -- Use simp to normalize the goal
      simp only [decomp_a1_aux, decomp_a2_aux, decomp_a3_aux, Nat.add_assoc, Nat.add_left_comm]
      -- After simp, LHS = a1 + (a2 + (a3 + (c1*3^k + (c2*3^k + c3*3^k))))
      -- Note c3 = 0, so c3*3^k = 0.
      -- First regroup: (a1 + a2) + (a3 + (c1*3^k + (c2*3^k + c3*3^k)))
      rw [← Nat.add_assoc (decomp_a1_aux ((n' + 1) / 3) (k + 1)) (decomp_a2_aux ((n' + 1) / 3) (k + 1)) (decomp_a3_aux ((n' + 1) / 3) (k + 1) + (decomp_a_c1 ((n' + 1) % 3) * 3 ^ k + (decomp_a_c2 ((n' + 1) % 3) * 3 ^ k + decomp_a_c3 ((n' + 1) % 3) * 3 ^ k)))]
      -- Second regroup: ((a1 + a2) + a3) + (c1*3^k + (c2*3^k + c3*3^k))
      rw [← Nat.add_assoc (decomp_a1_aux ((n' + 1) / 3) (k + 1) + decomp_a2_aux ((n' + 1) / 3) (k + 1)) (decomp_a3_aux ((n' + 1) / 3) (k + 1)) (decomp_a_c1 ((n' + 1) % 3) * 3 ^ k + (decomp_a_c2 ((n' + 1) % 3) * 3 ^ k + decomp_a_c3 ((n' + 1) % 3) * 3 ^ k))]
      -- Apply IH: ((a1 + a2) + a3) = 3^(k+1) * ((n'+1)/3)
      rw [ih ((n' + 1) / 3) (by omega) (k + 1)]
      -- Now LHS = 3^(k+1) * ((n'+1)/3) + (c1*3^k + (c2*3^k + c3*3^k))
      -- Step 1: c2*3^k + c3*3^k = (c2+c3)*3^k (c3 = 0, but we factor generally)
      rw [← Nat.add_mul (decomp_a_c2 ((n' + 1) % 3)) (decomp_a_c3 ((n' + 1) % 3)) (3 ^ k)]
      -- Step 2: c1*3^k + (c2+c3)*3^k = (c1+c2+c3)*3^k
      rw [← Nat.add_mul (decomp_a_c1 ((n' + 1) % 3)) (decomp_a_c2 ((n' + 1) % 3) + decomp_a_c3 ((n' + 1) % 3)) (3 ^ k)]
      -- Now LHS = 3^(k+1) * ((n'+1)/3) + (c1+c2+c3)*3^k
      simp only [Nat.add_assoc] at *
      rw [h_sum]
      rw [Nat.pow_succ 3 k]
      rw [Nat.mul_assoc (3 ^ k) 3 ((n' + 1) / 3)]
      rw [Nat.mul_comm ((n' + 1) % 3) (3 ^ k)]
      rw [← Nat.mul_add (3 ^ k) (3 * ((n' + 1) / 3)) ((n' + 1) % 3)]
      rw [Nat.div_add_mod]

-- Tests via native_decide:
example : decomp_a1_aux 7 0 + decomp_a2_aux 7 0 + decomp_a3_aux 7 0 = 7 := by native_decide
example : decomp_a1_aux 8 0 + decomp_a2_aux 8 0 + decomp_a3_aux 8 0 = 8 := by native_decide
example : decomp_a1_aux 100 0 + decomp_a2_aux 100 0 + decomp_a3_aux 100 0 = 100 := by native_decide
example : decomp_a1_aux 7 1 + decomp_a2_aux 7 1 + decomp_a3_aux 7 1 = 21 := by native_decide
example : decomp_a1_aux 100 1 + decomp_a2_aux 100 1 + decomp_a3_aux 100 1 = 300 := by native_decide

end Erdos125C
