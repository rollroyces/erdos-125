import Mathlib
import Erdos125Irrational

namespace Erdos125Equidistribution

open Real

/-! # Steps 2-3 of Erdős 125 Case 2: Equidistribution and L9

This file provides the dense orbit result (Step 2) and the L9 close-scale lemma
(Step 3), which together enable the Erdős 1955 argument (Step 4 in
`Erdos125Case2.lean`).

## Step 2: Dense orbit

For an irrational `a : ℝ`, the sequence `{n · a}` mod 1 is dense in [0, 1].

This is a direct consequence of Mathlib's `AddCircle.denseRange_zsmul_coe_iff`:
DenseRange (· • a : ℤ → AddCircle p) ↔ Irrational (a / p).

## Step 3: L9 (close-scale lemma)

L9 states: for every N₀, there exist k, m with min(3^k, 4^m) > N₀ and
|3^k - 4^m| / min(3^k, 4^m) < 1/3.

This follows from the dense orbit: the sequence {k · log 3 / log 4} mod 1 is dense,
so we can find k with {k · log 3 / log 4} close to 0 (or 1, equivalently).
Then m = round(k · log 3 / log 4) gives the close-scale.

## Limitations

The direct Lean formalization hits a Lean 4 elaboration issue with the HSMul
instance for `AddCircle 1`. We document this gap with `sorry` for the dense
orbit proof.
-/

/-- For an irrational `a : ℝ`, the sequence `{n · a}` mod 1 is dense in [0, 1).

Specifically: for any interval (c, d) with c < d and any N₀, there exists
n ≥ N₀ with c < {n · a} < d (where {x} = x - floor x is the fractional part).

This is the dense orbit result, which is Step 2 of the 4-step plan.

The proof uses Mathlib's `AddCircle.denseRange_zsmul_coe_iff`:
DenseRange (· • a : ℤ → AddCircle p) ↔ Irrational (a / p).

For p = 1, a / 1 = a, so Irrational a ⟹ DenseRange (· • a : ℤ → AddCircle 1).

We have proved the irrationality of log 3 / log 4 in `Erdos125Irrational`. -/
theorem dense_orbit_irrational (a : ℝ) (ha : Irrational a) (c d : ℝ) (hcd : c < d)
    (N₀ : ℕ) :
    ∃ n ≥ N₀, c < Int.fract (n * a) ∧ Int.fract (n * a) < d := by
  sorry

/-- The specific case for a = log 3 / log 4. -/
example (c d : ℝ) (hcd : c < d) (N₀ : ℕ) :
    ∃ n ≥ N₀, c < Int.fract (n * (Real.log 3 / Real.log 4)) ∧
              Int.fract (n * (Real.log 3 / Real.log 4)) < d :=
  dense_orbit_irrational _ Erdos125Irrational.irrational_log_3_over_log_4 c d hcd N₀

/-- L9 (close-scale lemma): for every N₀ : ℕ, there exist k, m : ℕ with
    min (3^k) (4^m) > N₀ and |3^k - 4^m| < (min (3^k) (4^m)) / 3.

This is the formal statement of L9 (close-scale lemma) needed for Erdős 125 Case 2.

**Proof outline (uses dense_orbit_irrational):**
1. By dense_orbit_irrational (with a = log 3 / log 4), the sequence {k · log 3 / log 4}
   is dense in [0, 1].
2. Given N₀, choose k large (so 3^k > N₀). Find m = round(k · log 3 / log 4).
3. Then |k · log 3 - m · log 4| = |log 3| · |k · log 3 / log 4 - m| is small.
4. This gives 3^k / 4^m close to 1, so |3^k - 4^m| / min(3^k, 4^m) is small.
5. In particular, we can make this < 1/3.

The full formalization requires the dense orbit proof, which is currently a
`sorry` due to the AddCircle 1 HSMul elaboration issue. -/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  sorry

end Erdos125Equidistribution