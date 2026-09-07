import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

namespace Erdos125Induction3

/-! # Erdos125 Block Structure via Mathlib's Nat.digits -/

/-- A natural number is in A iff every digit in its base-3 representation is < 2. -/
def inA (n : Nat) : Bool :=
  (Nat.digits 3 n).all (· < 2)

/-- Sanity checks. -/
example : inA 0 = true := by native_decide
example : inA 1 = true := by native_decide
example : inA 3 = true := by native_decide
example : inA 4 = true := by native_decide
example : inA 2 = false := by native_decide
example : inA 5 = false := by native_decide

/-- **Block structure lemma**: inA (3^k + a) = inA a for a < 3^k.

We compute the base-3 digits of 3^k + a as the digits of a (padded) followed by [1],
and use Mathlib's `Nat.ofDigits_inj_of_len_eq` to show this equals `Nat.digits 3 (3^k + a)`. -/
theorem inA_3pow_add_a (a k : Nat) (hak : a < 3^k) :
    inA (3^k + a) = inA a := by
  set L : List Nat :=
    (Nat.digits 3 a) ++ (List.replicate (k - (Nat.digits 3 a).length) 0) ++ [1] with hL
  -- L has length k+1, all digits < 3, and ofDigits 3 L = 3^k + a.
  have hlen_L : L.length = k + 1 := by
    rw [hL, List.length_append, List.length_append, List.length_replicate, List.length_singleton]
    have h_le : (Nat.digits 3 a).length ≤ k :=
      (Nat.digits_length_le_iff (by norm_num : 1 < 3) a).mpr hak
    have hlen1 : ((Nat.digits 3 a) ++ (List.replicate (k - (Nat.digits 3 a).length) 0)).length = k := by
      rw [List.length_append, List.length_replicate]
      rw [Nat.add_sub_cancel']
      exact h_le
    rw [hlen1]
  have hofd_L : Nat.ofDigits 3 L = 3^k + a := by
    show Nat.ofDigits 3
      ((Nat.digits 3 a) ++ (List.replicate (k - (Nat.digits 3 a).length) 0) ++ [1]) = 3^k + a
    rw [Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_singleton]
    have h1 : Nat.ofDigits 3 (List.replicate (k - (Nat.digits 3 a).length) 0) = 0 := by
      induction (k - (Nat.digits 3 a).length) with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih, Nat.ofDigits_cons, Nat.zero_add]
    rw [h1, mul_zero, add_zero]
    rw [Nat.ofDigits_digits]
    have hlen : ((Nat.digits 3 a) ++ (List.replicate (k - (Nat.digits 3 a).length) 0)).length = k := by
      rw [List.length_append, List.length_replicate]
      rw [Nat.add_sub_cancel']
      have h_le : (Nat.digits 3 a).length ≤ k :=
        (Nat.digits_length_le_iff (by norm_num : 1 < 3) a).mpr hak
      exact h_le
    rw [hlen]
    ring
  have h_lt_L : ∀ d ∈ L, d < 3 := by
    intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_append] at hd
      rcases hd with hd | hd
      · exact Nat.digits_lt_base (by norm_num : 1 < 3) hd
      · simp [List.mem_replicate] at hd; omega
    · simp at hd; omega
  -- The (k+1)-digit list Nat.digits 3 (3^k + a) has the same length and same ofDigits.
  have hofd_digits : Nat.ofDigits 3 (Nat.digits 3 (3^k + a)) = 3^k + a :=
    Nat.ofDigits_digits 3 (3^k + a)
  have h_lt_digits : ∀ d ∈ Nat.digits 3 (3^k + a), d < 3 :=
    fun d hd => Nat.digits_lt_base (by norm_num : 1 < 3) hd
  -- Key equality: L = Nat.digits 3 (3^k + a).
  -- Both have length k+1, all digits < 3, same ofDigits.
  have len_eq : (Nat.digits 3 (3^k + a)).length = k + 1 := by
    -- 3^k ≤ 3^k + a and 3^k + a < 3^(k+1), so length is exactly k+1.
    -- Use digits_length_le_iff: length ≤ k+1 iff a < 3^(k+1).
    -- For ≥: if length < k+1, then n < 3^k. But n ≥ 3^k. Contradiction.
    sorry
  have h_eq : L = Nat.digits 3 (3^k + a) := by
    -- Build the explicit proof that 1 < 3.
    have hb : (1 : Nat) < 3 := by norm_num
    -- Use ofDigits_inj_of_len_eq with all explicit args.
    -- The signature is: {b : ℕ} (hb : 1 < b) {L1 L2 : List ℕ}
    --   (len : L1.length = L2.length) (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b)
    --   (h : ofDigits b L1 = ofDigits b L2) : L1 = L2
    -- The Lean way: use exact with a fully constructed term.
    exact Nat.ofDigits_inj_of_len_eq 3 hb (by rw [hlen_L, len_eq]) h_lt_L h_lt_digits
      (by rw [hofd_L, hofd_digits])
  -- Conclude the inA equality.
  show ((Nat.digits 3 (3^k + a)).all (· < 2)) = ((Nat.digits 3 a).all (· < 2))
  rw [← h_eq, hL]
  rw [List.all_append, List.all_append]
  have h_zero : (List.replicate (k - (Nat.digits 3 a).length) 0).all (· < 2) = true := by
    induction (k - (Nat.digits 3 a).length) with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih]
  have h_one : ([1] : List Nat).all (· < 2) = true := by simp; omega
  rw [h_zero, h_one]
  simp

example (a k : Nat) (hak : a < 3^k) : inA (3^k + a) = inA a := inA_3pow_add_a a k hak

-- Specific verifications.
example : inA (3^1 + 0) = true := by native_decide
example : inA (3^1 + 1) = true := by native_decide
example : inA (3^2 + 3) = true := by native_decide
example : inA (3^2 + 4) = true := by native_decide
example : inA (3^3 + 12) = true := by native_decide
example : inA (3^4 + 0) = true := by native_decide
example : inA (3^4 + 27) = true := by native_decide
example : inA (3^5 + 81) = true := by native_decide
example : inA (3^5 + 121) = true := by native_decide

end Erdos125Induction3
