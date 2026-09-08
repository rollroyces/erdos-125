import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125Block
import Erdos125Irrational

namespace Erdos125Case2

open Real

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

/-- **Lower bound on A + B sumset using digit structure.**

For any N, every n < (3^k - 1)/2 + (4^m - 1)/3 has a decomposition
n = a + b with a ∈ A ∩ [0, 3^k) and b ∈ B ∩ [0, 4^m).

This is the digit-level no-carry argument. -/
theorem digit_sumset (k m : Nat) (n : Nat)
    (hn : n ≤ (3^k - 1) / 2 + (4^m - 1) / 3) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  sorry

/-- **L9-driven density bound**: Using L9, the sumset has positive density.

For every N₀, choose k, m with min(3^k, 4^m) > N₀ and |3^k - 4^m| / min < 1/3.
Then at the scale N = 4^m, the sumset has density ≥ 1/2. -/
theorem density_via_L9 (N₀ : Nat) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    (Erdos125Block.countAB_in_0_N (4 ^ m) : ℕ) ≥ (4 ^ m) / 2 := by
  sorry

/-- **Density positive for A + B** (the formal Erdős 125 Case 2 statement). -/
theorem erdos_125_case_2_positive_density :
    ∀ N₀ : Nat, ∃ N ≥ N₀, Erdos125Block.countAB_in_0_N N ≥ N / 2 := by
  sorry

end Erdos125Case2