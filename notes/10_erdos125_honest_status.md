# Erdős 125 Case 2: Honest Status After Numerical Analysis

**Date**: 2 September 2026
**Status**: STRONG numerical evidence for Case 2. Proof is research-level work.

## Numerical Findings

For N = 3^k (k = 1..14), density of A+B in [N, 2N):
- Minimum: 0.8751 (k=14)
- Maximum: 1.0000 (k=1, 2, 3)
- Always positive: density > 0.85 for all k.

This is overwhelming numerical evidence that Erdős 125 Case 2 is TRUE.

## What's Proved in Lean (so far)

1. |A ∩ [0, 3^k)| = 2^k for all k (via bijection)
2. |B ∩ [0, 4^k)| = 2^k for all k (via bijection)
3. inA (3n) = inA n (bijection)
4. inB (4n) = inB n (bijection)
5. Digit exclusion lemmas

## What's NOT proved (the gap)

The actual density statement: |A+B ∩ [3^k, 2 * 3^k)| ≥ c * 3^k for some c > 0.

This requires:
- A counting argument for A+B in [N, 2N)
- A bound on overlaps between different (a, b) decompositions
- A case analysis of A ∩ [0, N), A ∩ [N, 2N), B ∩ [0, N), B ∩ [N, 2N)

This is **research-level work**, not a single Lean session.

## What I Should Do Now

1. Be honest that the conjecture is not solved.
2. Document the counting infrastructure (DONE).
3. Document the numerical evidence.
4. Acknowledge the gap.

The conjecture Erdős 125 Case 2 is mathematically OPEN.
My Lean contribution: the counting infrastructure.
The numerical evidence strongly suggests Case 2.

## Mathematical Insight (Not Yet Proved)

The structural reason for the gap [463, 485]:
- The "all-1's" decomposition n = 121 + 341 = 462 (= 11111_3 + 11111_4) is the ONLY valid decomposition.
- For n ∈ [463, 485], no valid (a, b) pair exists.
- This is because:
  - b ∈ [0, 85] gives a ∈ [378, 485], but A ∩ [378, 484] = ∅.
  - b = 341 gives a ∈ [122, 144], but A ∩ [122, 144] = ∅.
  - Other b's not in B in this range.

The gap has length 23 = max(A) - max(B ∩ [0, N)) + ... something.

## Files

- /Users/hermes/.hermes/projects/erdos_125/lean_project/Erdos125.lean (counting)
- /Users/hermes/.hermes/projects/erdos_125/code/erdos_125_mathlib_proof.lean (copy)
- /Users/hermes/.hermes/projects/erdos_125/notes/06_full_induction_proof.md (counting)
- /Users/hermes/.hermes/projects/erdos_125/notes/09_density_direction.md (this is what I should write)
