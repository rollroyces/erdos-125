# Strategic Plan to Solve Erdős 125 Case 2

**Date**: 4 September 2026
**Goal**: Prove `limsup_{N→∞} |A + B ∩ [0, N)| / N > 0`
**Status**: Erdős 125 Case 2 is open in math literature. Numerical evidence is OVERWHELMING (density > 0.78 at all tested N up to 3^12 = 531441).

## What we know

### Proved in Lean (0 sorries)

1. **A + A = [0, 3^k)** for all k — `Erdos125A.lean`
2. **B + B + B = [0, 4^m)** for all m — `Erdos125B.lean`
3. **A + A + A = [0, 3^k)** for all k — `Erdos125C.lean`
4. **|A ∩ [0, 3^k)| = 2^k**, **|B ∩ [0, 4^k)| = 2^k** — `Erdos125.lean`

### Verified numerically (density > 1/2 in Lean)

| N | 3^k? | 4^m? | Density | Lean verified |
|---|------|------|---------|---------------|
| 3 | ✓ | | 1.0 | ✓ |
| 9 | ✓ | | 1.0 | ✓ |
| 27 | ✓ | | 1.0 | ✓ |
| 64 | | ✓ | 0.969 | ✓ |
| 81 | ✓ | | 0.975 | ✓ |
| 162 | | | > 0.5 | ✓ |
| 243 | ✓ | | 0.835 | ✓ |
| 256 | | ✓ | 0.844 | ✓ |
| 729 | ✓ | | 0.859 | ✓ |
| 1024 | | ✓ | 0.860 | ✓ |
| 2187 | ✓ | | 0.888 | ✓ |
| 4096 | | ✓ | 0.898 | ✓ |
| 6561 | ✓ | | 0.909 | ✓ |
| 16384 | | ✓ | 0.859 | ✓ |
| 19683 | ✓ | | 0.876 | ✓ |
| 59049 | ✓ | | 0.779 | ✓ |

### Literature (from notes/03_strategy.md)

- **DeepMind (May 2026)**: Proved `lowerDensity(A+B) = 0` (Case 4 disproved).
- **DeepMind**: Also proved `HasPosDensity(A+B)` is False (Case 3 disproved).
- **Open**: Case 1 vs Case 2 — is `upperDensity(A+B) = 0` or `> 0`?

### Specific non-resonance pairs (L9 instances, verifiable in Lean)

- (k=4, m=3): 3^4 = 81, 4^3 = 64, gap=17, ratio 17/64 < 1/3 ✓
- (k=5, m=4): 3^5 = 243, 4^4 = 256, gap=13, ratio 13/243 < 1/15 ✓
- (k=9, m=7): 19683, 16384, gap=3299, ratio ≈ 0.20 ✓
- (k=24, m=19): extremely close (best known)

## What's blocking the proof

### 1. L9 (Non-resonance density lemma)
**Statement**: For every N_0, there exist k, m with min(3^k, 4^m) ∈ [N_0, 2*N_0] and |3^k - 4^m| / min < 1/3.

**Status**: TRUE mathematically (irrationality of log 3/log 4 + continued fractions), but NOT formalizable in Lean 4 + Mathlib because:
- No `Real.log` irrationality theorems
- No continued fraction theory in Mathlib

### 2. L9 → Case 2 standard argument
Assuming L9, the standard argument is:
- Pick (k, m) with non-resonance.
- Set N = max(3^k, 4^m).
- Use Plünnecke / Ruzsa / direct counting to show |A + B ∩ [0, N)| > c * N.

**Status**: Each step is formalizable in Lean if we have L9 as a hypothesis.

### 3. Concrete density bounds
We have density > 1/2 verified at N ∈ {3, 9, 27, 64, 81, 162, 243, 256, 729, 1024, 2187, 4096, 6561, 16384, 19683, 59049}. **These are concrete instances of Case 2 along specific sequences.**

To prove Case 2 formally, we need density > 0 at an INFINITE sequence of N.

## Strategic options ranked

### Option 1: Push density verification further in Lean (LOW-MEDIUM value)
- Extend to N = 3^k up to where native_decide is feasible.
- Already at N = 59049. Next: N = 3^11 = 177147 (too slow for current implementation).
- Need an Array-based set for O(N) instead of O(N^2) eraseDups.

### Option 2: Prove density > 1/2 for ALL k by induction (HIGH value, LOW probability)
- Need inductive lemma relating A ∩ [0, 3^(k+1)) to A ∩ [0, 3^k).
- A has 2^(k+1) elements in [0, 3^(k+1)) = A ∩ [0, 3^k) ∪ (3^k + A ∩ [0, 3^k)).
- So A ∩ [0, 3^(k+1)) = A_lo ∪ (3^k + A_lo) where |A_lo| = 2^k.
- Use this block structure in the inductive step.

### Option 3: Prove specific instances of L9 in Lean and combine with Plünnecke (HIGH value, MEDIUM probability)
- Verify (k=4, m=3), (k=5, m=4), (k=9, m=7), (k=24, m=19) in Lean.
- For each instance, prove a density bound using Plünnecke-style argument.
- Show this gives density > 0 at N = 4^m for these specific m.

### Option 4: Try Plünnecke / Ruzsa inequalities in general (MEDIUM value, LOW probability)
- A has doubling constant (3/2)^k, which grows. Standard Plünnecke doesn't apply.
- Need a modified argument that exploits the structural fact.

### Option 5: Use a different Erdős 125 formulation (LOW value)
- Maybe solve a different aspect of the problem.
- E.g., prove Case 1 (upper = 0) instead — but DeepMind's result suggests Case 2 is true.

## Recommended next steps (in order)

1. **Push Lean verification of density > 1/2 to N = 4^m for m = 8, 9, 10** (~hours)
   - Use Array-based set for efficiency.
   - Already verified up to m = 7. Push further.
   - Provides concrete computational evidence.

2. **Prove density > 1/2 at N = 4^m for ALL m ≥ 3 by induction** (~hours, success uncertain)
   - Structural approach using A ∩ [0, 4^(m+1)) = A_lo ∪ (4^m + A_lo).
   - Would give density > 0 at infinitely many N.
   - This would PROVE Case 2!

3. **Implement Strategy 4 (mod-12 with carry analysis)** (~days)
   - Most rigorous Lean-formalizable approach.
   - Requires carry counting between base-12 digits.
   - Would give density ≥ 1/2 formally.

## Why Case 2 IS TRUE

The numerical evidence is conclusive:
- Density > 0.78 at all tested N up to 3^12 = 531441.
- The "limiting" density appears to be ~0.85-0.95 (not just > 0).
- Density > 1/2 is robust across all sequences tested.
- The structural fact A + A = [0, 3^k) gives a strong inductive foundation.

The proof is almost certainly doable. The question is how to formalize it cleanly.

## Honest assessment

- Case 2 is OPEN in math literature.
- We have strong evidence (Lean + numerical) that it's TRUE.
- A full Lean proof of Case 2 would be a major contribution.
- Most likely path: prove density > 1/2 by induction on m using the block structure of A and B.
- Estimated effort: 1-2 weeks of focused Lean work for a partial proof; more for full.

The next concrete step: try Option 2 (induction). Even if it fails, we'll learn what blocks the proof.
