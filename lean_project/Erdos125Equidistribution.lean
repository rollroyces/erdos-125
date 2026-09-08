import Mathlib
import Erdos125Irrational

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1 (Step 2)

Step 2 of the 4-step Erdős 125 Case 2 plan.

The dense orbit result (the sequence {n · a} is dense in AddCircle 1 for irrational a)
requires Mathlib's `AddCircle.denseRange_zsmul_coe_iff` lemma and its HSMul
instance for AddCircle 1, which has typeclass resolution issues in the current Mathlib
version. We document this as a known gap and proceed to Step 3 (L9) directly
using the existing infrastructure.

The "Weyl equidistribution" theorem itself (limiting distribution = Lebesgue measure)
is NOT in Mathlib. But the WEAKER statement we need for L9 (density, not
equidistribution) is supposed to be reachable via denseRange_zsmul_coe_iff.

## Step 3 (L9 - close-scale lemma) — informal proof sketch

The L9 lemma states: for every N₀, there exist k, m with min(3^k, 4^m) > N₀ and
|3^k - 4^m| / min(3^k, 4^m) < 1/3.

**Proof sketch**:
1. Consider the sequence α_n = {n · log 3 / log 4} (fractional part).
2. Since log 3 / log 4 is irrational (Erdos125Irrational), the dense orbit tells us
   α_n is dense in [0, 1].
3. Given any N₀, choose k large (so 3^k > N₀). Find m = round(k · log 3 / log 4).
4. Then |k · log 3 / log 4 - m| = |α_k - 0 or 1| can be made small (≤ 1/3 for large k).
5. From |k · log 3 - m · log 4| small, we get 3^k / 4^m close to 1, i.e., |3^k - 4^m| small.
6. After scaling, |3^k - 4^m| / min(3^k, 4^m) < 1/3.

The formalization of this in Lean is incomplete due to the AddCircle 1 HSMul
typeclass issue described above. -/

/-- Sketch: L9 lemma (close-scale).

For every N₀ : ℕ, there exist k, m : ℕ with min (3^k) (4^m) > N₀ and
|3^k - 4^m| < (min (3^k) (4^m)) / 3.

This is the formal statement of L9 (close-scale lemma) needed for Erdős 125 Case 2. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  sorry

end Erdos125Equidistribution