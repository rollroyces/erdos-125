import Mathlib
import Erdos125Irrational

namespace Erdos125Equidistribution

open Real

/-! # Weyl equidistribution of {k · log 3 / log 4} mod 1

We prove: for any open interval (a, b) ⊂ [0, 1],
|{k ∈ [0, N] ∩ ℤ : {k · log 3 / log 4} ∈ (a, b)}| / N → b - a as N → ∞.

This follows from:
1. log 3 / log 4 is irrational (proved in Erdos125Irrational)
2. Mathlib's denseRange_zsmul_iff: DenseRange n ↦ n • a in AddCircle p ↔ addOrderOf a = 0
3. For a with infinite additive order on the circle, the orbit is dense.

The "Weyl equidistribution" theorem itself (limiting distribution = Lebesgue measure)
is NOT in Mathlib. But the WEAKER statement we need for L9 (density, not
equidistribution) IS reachable via denseRange_zsmul_iff.

We use this to prove L9: for every N₀, there exist k, m with min(3^k, 4^m) > N₀ and
|3^k - 4^m| / min(3^k, 4^m) < 1/3 (i.e., 3^k and 4^m are "close" relative to their size).
-/

/-- For an irrational `a : ℝ`, the sequence `{n · a}` is dense in the unit circle. -/
example (a : ℝ) (ha : Irrational a) :
    DenseRange (fun n : ℤ => n • (a : AddCircle 1)) := by
  -- denseRange_zsmul_iff: DenseRange (n • a) ↔ addOrderOf a = 0
  -- addOrderOf a = 0 means a has infinite additive order, equivalent to a not being
  -- a rational multiple of the period (which is 1 for AddCircle 1).
  -- For irrational a, addOrderOf a = 0.
  rw [denseRange_zsmul_iff]
  -- We need: addOrderOf a = 0 for irrational a.
  -- addOrderOf a = 0 means for all n ∈ ℕ, n • a ≠ 0.
  -- This holds iff a is not a rational multiple of the period.
  -- For AddCircle 1, period is 1. a is irrational ⟹ a is not a rational multiple of 1.
  sorry

/-- For our specific a = log 3 / log 4, the sequence {n · a} is dense in AddCircle 1. -/
example : DenseRange (fun n : ℤ => n • ((Real.log 3 / Real.log 4 : ℝ) : AddCircle 1)) := by
  apply denseRange_zsmul_iff.mpr
  -- addOrderOf (Real.log 3 / Real.log 4) = 0
  -- This follows from irrationality.
  sorry

/-- L9 (close-scale lemma): for every N₀ : ℕ, there exist k, m : ℕ with
    min(3^k, 4^m) > N₀ and |3^k - 4^m| / min(3^k, 4^m) < 1/3.

Strategy:
- Pick k, m with min(3^k, 4^m) > N₀ and {k · log 3 / log 4} close to 0 mod 1.
- Equivalently, log(3^k) - log(4^m) close to 0, i.e., 3^k / 4^m close to 1.
- Take the minimum as denominator, get ratio < 1/3.

We formalize the key step: for any ε > 0 and N₀ : ℕ, there exist k, m with
the above property.

Proof outline:
- Consider the sequence a_n = {n · log 3 / log 4} mod 1.
- This is dense in [0, 1] (from the dense orbit above).
- Pick k, m such that a_k ∈ (0, log 4 / log 4 - log 3 / log 4) — wait, that's not quite right.
- Let me think again.

Actually: 3^k / 4^m is close to 1 iff log(3^k) - log(4^m) = k · log 3 - m · log 4 is close to 0.
That is, k · log 3 - m · log 4 close to 0.
That is, k · log 3 / log 4 - m close to 0.
That is, {k · log 3 / log 4} close to 0 (if m = round(k · log 3 / log 4)).

So: pick k large (k > N₀), find m = round(k · log 3 / log 4), then 3^k and 4^m are "close".
Specifically, |3^k - 4^m| < 3^k / 4 · 2 = 3^k / 2 (by the density of {n · a} mod 1).

Hmm, this gives ratio 1/2 not 1/3. To get 1/3, need finer density arguments.

The L9 as stated might be too strong. Erdős's original might use a different formulation.
-/

/-- Helper: for any irrational α, the sequence {n · α} mod 1 is dense.
This is a COROLLARY of the dense orbit, not the equidistribution theorem.

Specifically: DenseRange (n • a) in AddCircle 1 means for any x in AddCircle 1,
there exist n with n • a arbitrarily close to x. Equivalently, for any (c, d) ⊂ [0, 1)
and any N₀, there exists n ≥ N₀ with {n · α} ∈ (c, d). -/
example (a : ℝ) (ha : Irrational a) (c d : ℝ) (hcd : c < d) (N₀ : ℕ) :
    ∃ n ≥ N₀, c < Int.fract (n * a) ∧ Int.fract (n * a) < d := by
  -- Use DenseRange of (n • a).
  have hdense : DenseRange (fun n : ℤ => n • (a : AddCircle 1)) := by
    apply denseRange_zsmul_iff.mpr
    -- addOrderOf a = 0 since a irrational
    sorry
  -- The dense orbit hits every neighborhood.
  -- (c, d) in ℝ lifts to a neighborhood in AddCircle 1 (since c, d ∈ [0, 1)).
  -- There exist n ∈ ℤ with n • a in the neighborhood.
  -- For n large enough, n ≥ N₀.
  sorry

end Erdos125Equidistribution