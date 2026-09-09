import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125CountAB
import Erdos125Equidistribution
import Erdos125Irrational

namespace Erdos125Case2

open Erdos125 Erdos125A Erdos125B Erdos125CountAB Erdos125Equidistribution Real

/-! # Erdős 125 Case 2 (Step 4)

This file proves Erdős 125 Case 2:
lim sup_{N→∞} |A + B ∩ [0, N)| / N > 0.

The proof combines the structural infrastructure with the L9 lemma (Step 3)
which itself depends on equidistribution (Step 2) and irrationality (Step 1).

## Erdős 1955 argument (informal)

For every N₀, by L9, there exist k, m with min(3^k, 4^m) > N₀ and
|3^k - 4^m| / min(3^k, 4^m) < 1/3.

WLOG 3^k ≤ 4^m (otherwise swap). Then 3^k / 4^m ≥ 1/2 (close to 1).

Consider the intervals:
- I = [0, 4^m) of length 4^m.
- We want to count |A + B ∩ I|.

By the structural facts (A + A = [0, 3^k), B + B + B = [0, 4^m)):
- A ⊇ A ∩ [0, 3^k), with |A ∩ [0, 3^k)| = 2^k elements, all ≤ (3^k - 1)/2.
- B ⊇ B ∩ [0, 4^m), with |B ∩ [0, 4^m)| = 2^m elements, all ≤ (4^m - 1)/3.

For n ∈ [0, 4^m), write n = a + b with a ∈ A, b ∈ B (this is the goal).
By the digit decomposition structure, for n < (3^k - 1)/2 + (4^m - 1)/3:
- n = a + b can be achieved with a ∈ A and b ∈ B (no carry in base 12 = lcm(3, 4)).

The ratio (3^k - 1)/2 + (4^m - 1)/3 ≈ 3^k/2 + 4^m/3 ≈ 5·4^m/6 = 5/6 (since 3^k ≈ 4^m).

So |A + B ∩ [0, 4^m)| ≥ (5/6) · 4^m, giving density ≥ 5/6.

This is much stronger than density > 0.

## Formal structure

Step 4 has three main lemmas:
1. **digit_sumset**: For n < 3^k, n can be written as a + b with a ∈ A ∩ [0, 3^k), b ∈ B ∩ [0, 4^m), where m is chosen by L9.
2. **count_via_L9**: Using L9, |A + B ∩ [0, N)| ≥ c·N for some c > 0.
3. **density_positive**: lim sup > 0.

The full proof is INCOMPLETE due to the AddCircle 1 HSMul issue blocking Step 2,
and the formal digit-sumset argument requires additional infrastructure (no-carry
representation in mixed base).

We provide partial progress below. -/

/-- **Digit-sumset**: structural lemma needed for Step 4.

We leave this as a `sorry` because the formal digit-level no-carry argument
requires substantial additional Lean infrastructure (mixed base representation,
no-carry decomposition). This lemma is **not strictly required** for the
density result; we use a separate numerical verification (in
`Erdos125CountAB`) for the density bound.

The full Erdős 1955 digit-sumset argument: for n < 3^k, write n in base 3
(digits 0, 1, 2). Split each base-3 digit as a sum of a base-3 digit (for A)
and a base-4 digit (for B). The "no-carry" decomposition gives n = a + b with
a ∈ A, b ∈ B.

**Honest status**: This is BLOCKED and requires significant additional Lean
formalization. -/
theorem digit_sumset (k m : Nat) (n : Nat) (hn : n < 3^k) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  sorry

/-- **L9-driven density bound**: Using L9, the sumset has positive density.

For every N₀, choose k, m with min(3^k, 4^m) > N₀ and |3^k - 4^m| / min < 1/3.
Then at the scale N = 4^m, the sumset has density ≥ 1/2.

**Honest status**: This proof is incomplete. The L9 lemma (Step 3) gives
∃ n m : ℤ, |3^|n| - 4^|m|| · 3 < min(3^|n|, 4^|m|), but does not guarantee
min(3^|n|, 4^|m|) > N₀. The full proof requires either:
(a) the Erdős 1955 self-similarity argument, or
(b) `native_decide` on `countAB_in_0_N (4^(N₀+1))` for symbolic N₀ (unsupported).

We provide a PARTIAL proof for small N₀ below. -/
theorem density_via_L9 (N₀ : Nat) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    (Erdos125CountAB.countAB_in_0_N (4 ^ m) : ℕ) ≥ (4 ^ m) / 2 := by
  -- PARTIAL PROOF: only works for N₀ ≤ 16.
  -- For larger N₀, the proof is BLOCKED (see notes/35_STEP4_HONEST_STATUS.md).
  by_cases hN : N₀ ≤ 26
  · refine ⟨3, 3, ?_, ?_⟩
    · -- Goal: min (3^3) (4^3) > N₀. Compute 3^3 = 27, 4^3 = 64, then min 27 64 = 27.
      have h27_le_64 : (27 : ℕ) ≤ 64 := by norm_num
      rw [show (3 ^ 3 : ℕ) = 27 from by norm_num,
          show (4 ^ 3 : ℕ) = 64 from by norm_num,
          Nat.min_eq_left h27_le_64]
      omega
    · -- countAB_in_0_N 64 ≥ 32 (verified by native_decide)
      native_decide
  · sorry

/-- **Density positive for A + B** (the formal Erdős 125 Case 2 statement).

For every N₀, we produce N = 4^m with m from `density_via_L9`. Since
min(3^k, 4^m) > N₀ implies 4^m > N₀ (because min ≤ 4^m), we have
N ≥ N₀ + 1 ≥ N₀, so N ≥ N₀.

**Honest status**: This proof is BLOCKED for large N₀ because `density_via_L9`
itself is blocked (only works for N₀ ≤ 26). For N₀ ≤ 26, the proof is complete. -/
theorem erdos_125_case_2_positive_density :
    ∀ N₀ : Nat, ∃ N ≥ N₀, Erdos125CountAB.countAB_in_0_N N ≥ N / 2 := by
  intro N₀
  obtain ⟨k, m, hmin, hcount⟩ := density_via_L9 N₀
  -- hmin : min (3 ^ k) (4 ^ m) > N₀ implies 4^m > N₀ (since min ≤ 4^m).
  -- In Nat, x > y implies x ≥ y + 1.
  have hgt : 4 ^ m > N₀ := lt_of_lt_of_le hmin (Nat.min_le_right _ _)
  -- So 4^m ≥ N₀ + 1, hence 4^m ≥ N₀.
  exact ⟨4 ^ m, Nat.le_of_lt hgt, hcount⟩

end Erdos125Case2