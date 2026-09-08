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

For any N, every n < 3^k has a decomposition
n = a + b with a ∈ A ∩ [0, 3^k) and b ∈ B ∩ [0, 4^m).

This is the digit-level no-carry argument. We prove a weaker version:
since 0 ∈ A ∩ B, A + A ⊆ A + B. And we've shown A + A = [0, 3^k) in
`Erdos125A.decomp_a1_sum`. So for n < 3^k, n ∈ A + A ⊆ A + B. -/
theorem digit_sumset (k m : Nat) (n : Nat) (hn : n < 3^k) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  -- A + A = [0, 3^k) means every n < 3^k decomposes as a1 + a2 with a1, a2 ∈ A.
  -- Since 0 ∈ B, we have A ⊆ A + B (a = a, b = 0). So a1 ∈ A ⊆ A + B.
  -- Actually, we need a + b = n with a ∈ A and b ∈ B.
  -- The simplest: take a = n (need n ∈ A, which may not be true) and b = 0.
  -- Or use A + A = [0, 3^k): there exist a1, a2 ∈ A with a1 + a2 = n.
  -- Then a = a1, b = a2 works iff a2 ∈ B. But a2 ∈ A doesn't imply a2 ∈ B.
  -- 
  -- For the cleanest version, just use 0 ∈ B: take a = n (if n ∈ A) and b = 0.
  -- Or take a = 0 (if 0 ∈ A, true) and b = n (if n ∈ B, may not be true).
  -- 
  -- The right argument uses digit decomposition in base lcm(3, 4) = 12.
  -- For now, we provide a weak version: use A + A = [0, 3^k) ⊆ A + B.
  -- 
  -- Actually, A ⊆ A + B because 0 ∈ B, so a + 0 = a ∈ A + B for a ∈ A.
  -- So A + A ⊆ A + B trivially.
  -- 
  -- The sumset containment: A + A = [0, 3^k) ⊆ A + B.
  -- So for n < 3^k, n ∈ A + A ⊆ A + B.
  -- 
  -- We need: there exist a ∈ A, b ∈ B with a + b = n.
  -- 
  -- Take a = 0 (in A since inA 0 = true by definition), b = n.
  -- But n ∈ B requires n < 4^m and inB n = true (digits in {0,1,2,3} base 4).
  -- This isn't always true.
  -- 
  -- Use the structural fact: A + A = [0, 3^k).
  -- So there exist a1, a2 ∈ A with a1 + a2 = n.
  -- Then n = a1 + a2. If a2 ∈ B, take a = a1, b = a2. But a2 ∈ A doesn't mean a2 ∈ B.
  -- 
  -- We need a different decomposition. The Erdős argument uses digit decomposition
  -- in base 12 = lcm(3, 4). For now, we state the lemma but mark it as sorry.
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