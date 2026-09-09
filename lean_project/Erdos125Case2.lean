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

/-- **Digit-sumset**: structural lemma (NOT on the critical path for Step 4).

For n < 3^k, n can be written as a + b with a ∈ A, b ∈ B, a < 3^k, b < 4^m.

**Honest status**: This is left as `sorry`. The critical-path theorems
(`density_via_L9` and `erdos_125_case_2_positive_density`) do NOT depend on
this lemma — they use direct numerical verification via `countAB_in_0_N`.

The digit-level no-carry argument requires formalizing mixed base representation,
which is substantial Lean work outside the scope of Step 4. -/
theorem digit_sumset (k m : Nat) (n : Nat) (hn : n < 3^k) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  sorry

/-- **L9-driven density bound**: Using L9, the sumset has positive density.

For every N₀, choose k, m with min(3^k, 4^m) > N₀ and |3^k - 4^m| / min < 1/3.
Then at the scale N = 4^m, the sumset has density ≥ 1/2.

**Honest status**: This proof uses `native_decide` on a specific N₀ threshold.
The proof is complete for N₀ below the threshold (currently 4^6 = 4096).
Extending to larger N₀ requires either:
(a) the Erdős 1955 self-similarity argument, or
(b) `native_decide` on `countAB_in_0_N (4^(N₀+1))` for symbolic N₀ (unsupported). -/
theorem density_via_L9 (N₀ : Nat) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    (Erdos125CountAB.countAB_in_0_N (4 ^ m) : ℕ) ≥ (4 ^ m) / 2 := by
  -- PARTIAL PROOF: works for N₀ < 65536 (= 4^8).
  -- For larger N₀, the proof is BLOCKED (see notes/36_STEP4_PARTIAL.md).
  by_cases hN : N₀ < 65536
  · -- Pick k = 10, m = 8. 3^10 = 59049, 4^8 = 65536.
    -- min(59049, 65536) = 59049. Need 59049 > N₀. ✓ for N₀ < 65536 (since 59049 < 65536).
    -- Wait, we need 59049 > N₀, which is N₀ ≤ 59048. For N₀ in [59049, 65535] we fail.
    -- Better: pick k = 11, m = 8. 3^11 = 177147, 4^8 = 65536.
    -- min(177147, 65536) = 65536. ✓ for N₀ < 65536.
    refine ⟨11, 8, ?_, ?_⟩
    · -- min (3^11) (4^8) = min 177147 65536 = 65536. Need 65536 > N₀.
      have h11 : (3^11 : ℕ) = 177147 := by norm_num
      have h8 : (4^8 : ℕ) = 65536 := by norm_num
      have hle : (65536 : ℕ) ≤ 177147 := by norm_num
      rw [h11, h8, Nat.min_eq_right hle]
      exact hN
    · -- countAB_in_0_N 65536 ≥ 32768 (verified by native_decide in 367s)
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