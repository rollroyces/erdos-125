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

theorem decomp_c_le_one (d : Nat) (hd : d < 3) : decomp_c d ≤ 1 := by
  interval_cases d <;> simp [decomp_c, decomp_r]
theorem decomp_r_le_one (d : Nat) (hd : d < 3) : decomp_r d ≤ 1 := by
  interval_cases d <;> simp [decomp_c, decomp_r]
theorem decomp_sum (d : Nat) (hd : d < 3) : decomp_c d + decomp_r d = d := by
  interval_cases d <;> simp [decomp_c, decomp_r]

/-- **Helper (CLOSED)**: decomp_a1_aux n k = 3^k * decomp_a1_aux n 0. -/
theorem decomp_a1_aux_eq (n k : Nat) : decomp_a1_aux n k = 3^k * decomp_a1_aux n 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    match n with
    | 0 => simp [decomp_a1_aux]
    | n' + 1 =>
      simp only [decomp_a1_aux]
      have h_lt : (n' + 1) / 3 < n' + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      have ih1 := ih ((n' + 1) / 3) h_lt (k + 1)
      have ih2 := ih ((n' + 1) / 3) h_lt 1
      rw [ih1, ih2]
      rw [mul_add, ← mul_assoc]
      simp only [pow_one]
      ring

/-- **Helper (CLOSED)**: decomp_a2_aux n k = 3^k * decomp_a2_aux n 0. -/
theorem decomp_a2_aux_eq (n k : Nat) : decomp_a2_aux n k = 3^k * decomp_a2_aux n 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    match n with
    | 0 => simp [decomp_a2_aux]
    | n' + 1 =>
      simp only [decomp_a2_aux]
      have h_lt : (n' + 1) / 3 < n' + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      have ih1 := ih ((n' + 1) / 3) h_lt (k + 1)
      have ih2 := ih ((n' + 1) / 3) h_lt 1
      rw [ih1, ih2]
      rw [mul_add, ← mul_assoc]
      simp only [pow_one]
      ring

/-- **MAIN RESULT (CLOSED)**: decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n. -/
theorem decomp_a1_sum : ∀ n k : Nat, decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n := by
  intro n k
  -- Use suffices: prove the base case k=0, then reduce general k.
  suffices hk0 : decomp_a1_aux n 0 + decomp_a2_aux n 0 = n by
    -- General k: factor 3^k via decomp_aN_aux_eq.
    rw [decomp_a1_aux_eq n k, decomp_a2_aux_eq n k]
    rw [← mul_add, hk0]
  -- Prove the base case k=0.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [decomp_a1_aux, decomp_a2_aux]
    | n' + 1 =>
      have h_lt : (n' + 1) / 3 < n' + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      have ih1 := ih ((n' + 1) / 3) h_lt
      simp only [decomp_a1_aux, decomp_a2_aux, pow_zero, mul_one, Nat.zero_add]
      -- Goal: a1' + (c1 + (a2' + c2)) = n' + 1
      -- where a1' = decomp_a1_aux ((n'+1)/3) 1, a2' = decomp_a2_aux ((n'+1)/3) 1,
      --       c1 = decomp_c d, c2 = decomp_r d.
      -- Convert a1' = 3*a1'', a2' = 3*a2'' via decomp_a1_aux_eq at k=1.
      have e_a1 : decomp_a1_aux ((n' + 1) / 3) 1 = 3 * decomp_a1_aux ((n' + 1) / 3) 0 :=
        decomp_a1_aux_eq ((n' + 1) / 3) 1
      have e_a2 : decomp_a2_aux ((n' + 1) / 3) 1 = 3 * decomp_a2_aux ((n' + 1) / 3) 0 :=
        decomp_a2_aux_eq ((n' + 1) / 3) 1
      rw [e_a1, e_a2]
      -- Goal: 3*a1'' + (c1 + (3*a2'' + c2)) = n' + 1
      -- Apply ih1: a1'' + a2'' = (n'+1)/3.
      -- Reassociate: 3 * (a1'' + a2'') + c1 + c2 = 3 * (n'+1)/3 + (n'+1) % 3.
      -- Use Nat.add_left_comm: x + (y + (z + w)) = y + (x + (z + w)) (swap x and y).
      -- Actually: 3*a1'' + (c1 + (3*a2'' + c2)) -> reorder to (a1'' + a2'') form.
      rw [Nat.add_assoc]
      -- 3*a1'' + (c1 + 3*a2'') + c2 — hmm, doesn't help.
      -- Instead, swap b and c1: 3*a1'' + c1 + (3*a2'' + c2) = 3*a1'' + 3*a2'' + c1 + c2.
      -- But this is left-assoc: ((3*a1'' + c1) + 3*a2'') + c2. After Nat.add_assoc: (3*a1'' + c1 + 3*a2'') + c2.
      -- To swap, use Nat.add_left_comm: a + (b + c) = b + (a + c). Apply to inner: c1 + (3*a2'') = 3*a2'' + c1.
      rw [Nat.add_left_comm (decomp_c ((n' + 1) % 3)) (3 * decomp_a2_aux ((n' + 1) / 3) 0) (decomp_r ((n' + 1) % 3))]
      -- Now: 3*a1'' + (3*a2'' + (c1 + c2)).
      -- We want: 3*(a1'' + a2'') + (c1 + c2).
      -- Use ac_rfl to reorder via add_comm + add_assoc:
      have heq1 : (3 * decomp_a1_aux ((n' + 1) / 3) 0 + 3 * decomp_a2_aux ((n' + 1) / 3) 0) +
                  (decomp_c ((n' + 1) % 3) + decomp_r ((n' + 1) % 3)) =
                  3 * decomp_a1_aux ((n' + 1) / 3) 0 +
                  (3 * decomp_a2_aux ((n' + 1) / 3) 0 +
                    (decomp_c ((n' + 1) % 3) + decomp_r ((n' + 1) % 3))) := by
        rw [Nat.add_assoc]
      rw [← heq1]
      rw [← Nat.mul_add]  -- 3*a1 + 3*a2 = 3*(a1 + a2)
      rw [ih1]
      have hsum : decomp_c ((n' + 1) % 3) + decomp_r ((n' + 1) % 3) = (n' + 1) % 3 :=
        decomp_sum ((n' + 1) % 3) (Nat.mod_lt _ (by norm_num : 0 < 3))
      rw [hsum, Nat.div_add_mod]

/-- **Helper (CLOSED)**: inA (3 * n) = true when inA n = true. -/
theorem inA_mul_three (n : Nat) (h : inA n = true) : inA (3 * n) = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [inA]
    | n' + 1 =>
      have h_eq : (3 * (n' + 1)) = (3 * (n' + 1) - 1) + 1 := by omega
      rw [h_eq]
      rw [inA.eq_2]
      have h_simp : (3 * (n' + 1) - 1) + 1 = 3 * (n' + 1) := by omega
      rw [h_simp]
      have hmod : (3 * (n' + 1)) % 3 = 0 := by omega
      have hdiv : (3 * (n' + 1)) / 3 = n' + 1 := by omega
      rw [hmod, hdiv]
      exact h

/-- **Helper (CLOSED)**: inA (3^k * n) = true when inA n = true. -/
theorem inA_mul_three_pow (k n : Nat) (h : inA n = true) : inA (3^k * n) = true := by
  induction k with
  | zero => simp [pow_zero, h]
  | succ k ih =>
    rw [pow_succ]
    -- Goal: inA (3^k * 3 * n) = true
    have hmul := inA_mul_three (3^k * n) ih
    -- hmul : inA (3 * (3^k * n)) = true
    -- 3 * (3^k * n) = 3^k * 3 * n by ring.
    have heq : 3 * (3^k * n) = 3^k * 3 * n := by ring
    rw [heq] at hmul
    exact hmul

/-- **Helper (CLOSED)**: inA (3a + c) = true when a ∈ A and c ∈ {0, 1}. -/
theorem inA_3a_plus_c (a c : Nat) (ha : inA a = true) (hc : c < 2) :
    inA (3 * a + c) = true := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
      simp [inA]
      cases c with
      | zero => simp [inA]
      | succ c =>
        cases c with
        | zero =>
          rw [inA]
          simp [inA]
        | succ _ => omega
    | a' + 1 =>
      have h_eq : (3 * (a' + 1) + c) = (3 * (a' + 1) + c - 1) + 1 := by omega
      rw [h_eq]
      rw [inA.eq_2]
      have h_simp : (3 * (a' + 1) + c - 1) + 1 = 3 * (a' + 1) + c := by omega
      rw [h_simp]
      cases c with
      | zero =>
        have hmod : (3 * (a' + 1)) % 3 = 0 := by omega
        have hdiv : (3 * (a' + 1)) / 3 = a' + 1 := by omega
        -- First, simplify (3 * (a' + 1) + 0) to (3 * (a' + 1)).
        rw [Nat.add_zero]
        rw [hmod, hdiv]
        exact ha
      | succ c =>
        cases c with
        | zero =>
          have hmod : (3 * (a' + 1) + 1) % 3 = 1 := by omega
          have hdiv : (3 * (a' + 1) + 1) / 3 = a' + 1 := by omega
          rw [hmod, hdiv]
          exact ha
        | succ _ => omega

/-- **Helper (CLOSED)**: decomp_a1_aux n 0 ∈ A. -/
theorem decomp_a1_aux_0_inA (n : Nat) : inA (decomp_a1_aux n 0) = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [decomp_a1_aux, inA]
    | n' + 1 =>
      simp only [decomp_a1_aux]
      simp only [pow_zero, mul_one]
      have ih_app := ih ((n' + 1) / 3) (Nat.div_lt_self (Nat.succ_pos _) (by norm_num))
      rw [decomp_a1_aux_eq ((n' + 1) / 3) 1]
      simp only [pow_one]
      have hc_lt : decomp_c ((n' + 1) % 3) < 2 := by
        rw [decomp_c]
        cases hmod : (n' + 1) % 3 with
        | zero => simp
        | succ d =>
          cases d with
          | zero => simp
          | succ d =>
            cases d with
            | zero => simp
            | succ _ => omega
      exact inA_3a_plus_c (decomp_a1_aux ((n' + 1) / 3) 0)
        (decomp_c ((n' + 1) % 3)) ih_app hc_lt

/-- **CLOSED**: decomp_a1_aux n k ∈ A for all k. -/
theorem decomp_a1_aux_inA (n k : Nat) : inA (decomp_a1_aux n k) := by
  rw [decomp_a1_aux_eq]
  exact inA_mul_three_pow k _ (decomp_a1_aux_0_inA n)

/-- **Helper (CLOSED)**: decomp_a2_aux n 0 ∈ A. -/
theorem decomp_a2_aux_0_inA (n : Nat) : inA (decomp_a2_aux n 0) = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [decomp_a2_aux, inA]
    | n' + 1 =>
      simp only [decomp_a2_aux]
      simp only [pow_zero, mul_one]
      have ih_app := ih ((n' + 1) / 3) (Nat.div_lt_self (Nat.succ_pos _) (by norm_num))
      rw [decomp_a2_aux_eq ((n' + 1) / 3) 1]
      simp only [pow_one]
      have hc_lt : decomp_r ((n' + 1) % 3) < 2 := by
        rw [decomp_r, decomp_c]
        cases hmod : (n' + 1) % 3 with
        | zero => simp
        | succ d =>
          cases d with
          | zero => simp
          | succ d =>
            cases d with
            | zero => simp
            | succ _ => omega
      exact inA_3a_plus_c (decomp_a2_aux ((n' + 1) / 3) 0)
        (decomp_r ((n' + 1) % 3)) ih_app hc_lt

/-- **CLOSED**: decomp_a2_aux n k ∈ A for all k. -/
theorem decomp_a2_aux_inA (n k : Nat) : inA (decomp_a2_aux n k) := by
  rw [decomp_a2_aux_eq]
  exact inA_mul_three_pow k _ (decomp_a2_aux_0_inA n)

end Erdos125A