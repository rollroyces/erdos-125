# Density vs Structural Facts: Reconciling the Numbers

**Date**: 4 September 2026

## The apparent contradiction

The structural fact (proved in Lean) is:
**A + A = [0, 3^k)** for all k.

This means every n < 3^k is in A + A.

But the density file shows:
**countAB_in_0_N 81 = 79** (not 81).

So 62, 63 ∉ A + B, even though 62, 63 ∈ A + A ⊂ [0, 81).

## Resolution

A + A ⊄ A + B. Just because a + a' is a sum of TWO A-elements doesn't mean it's a sum of
one A-element and one B-element.

Example: 62 = 31 + 31, both 31 ∈ A (since 31 = 1011_3). But 31 ∉ B (since 31 = 133_4 has digits 1, 3, 3 with 3 > 1).

So 62 = a + a' but 62 ≠ α + β with α ∈ A, β ∈ B (we verified computationally).

## What the structural fact DOES give us

A + A = [0, 3^k) means: for any "shift" b ∈ B, the set b + (A + A) = {b + a + a' : a, a' ∈ A} ⊂ A + B.

But this set is not [b, b + 3^k) — it's the sumset b + [0, 3^k), which IS [b, b + 3^k).

So [b, b + 3^k) ⊂ A + B for every b ∈ B?

Let me check: for b = 0, [0, 81) ⊂ A + B? But we have 62, 63 missing.

So [0, 3^k) is NOT in A + B. The containment [b, b + 3^k) ⊂ A + B fails for b = 0.

Wait — why? Because A + A is a subset of A + A, not A + B.

(Because we need a + a' with a, a' ∈ A, but A + B requires α + β with α ∈ A, β ∈ B. Different!)

## What A + A = [0, 3^k) actually means

The fact is that for every n ∈ [0, 3^k), there EXIST a, a' ∈ A with a + a' = n.

This DOES NOT mean [0, 3^k) ⊂ A + B.

## What's actually true

Numerical verification (all checked by native_decide in Lean):
- N=3: density 1.0
- N=9: density 1.0
- N=27: density 1.0
- N=81: density 79/81 ≈ 0.975
- N=162: density > 1/2
- N=243: density 203/243 ≈ 0.835
- N=729: density 626/729 ≈ 0.859
- N=2187: density ≈ 0.888

So density > 1/2 for all tested N up to 3^7.

But density is NOT 1.0 for N ≥ 81. There are gaps.

## Why the gaps?

For n to be in A + B, we need n = a + b with a ∈ A (digits 0/1 in base 3), b ∈ B (digits 0/1 in base 4).

The constraint that a has only 0/1 digits in base 3 AND b has only 0/1 digits in base 4 is strong.

For large n, the digit constraints from both bases interact and create "carry" failures.

## How to prove positive upper density (Erdős 125 Case 2)

Numerical evidence: density ≥ 0.83 for tested N up to 3^7.

The mod-12 argument (Strategy 4 in notes/16) gives density ≥ 1/2 if we can show:
"Every n with all base-12 digits in {0, 1, 2, 4, 5, 6} is in A + B."

But carries between base-12 digits break this argument.

The real proof likely uses the structural facts more cleverly — perhaps combining
A + A and B + B + B to give a stronger bound.

## Lean-verified concrete progress

**5 Lean files, 0 sorries:**
1. Erdos125.lean: counting
2. Erdos125A.lean: A + A = [0, 3^k)
3. Erdos125B.lean: B + B + B = [0, 4^m)
4. Erdos125C.lean: A + A + A = [0, 3^k)
5. Erdos125Density.lean: density > 1/2 at N = 3, 9, 27, 81, 162, 243, 729, 2187

The structural facts are USEFUL for Erdős 125 Case 2, but the final density proof remains open.
