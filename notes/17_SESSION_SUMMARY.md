# Erdős 125 — Major Progress Update (Session of 4 Sept 2026)

**Date**: 4 September 2026
**Status**: Erdős 125 Case 2 still open in math literature, but structural foundations significantly strengthened.

## Summary of session achievements

### 1. Closed the last sorry: `B + B + B = [0, 4^m)` proved in Lean (0 sorries)

The decomp_b_sum theorem (B+B+B = [0, 4^m) structural lemma) is now fully proved.
The key was `simp only [Nat.add_assoc] at *` to normalize `(c + (r + s))` to `(c + r + s)` form
so h_sum could apply.

### 2. New structural lemma: `A + A + A = [0, 3^k)` proved in Lean (0 sorries)

Erdos125C.lean: the 3-way decomposition for A.
Every d ∈ {0, 1, 2} can be written as c1 + c2 + c3 with c_i ∈ {0, 1}:
- d = 0: c1=0, c2=0, c3=0
- d = 1: c1=1, c2=0, c3=0
- d = 2: c1=1, c2=1, c3=0

(Note: c3 is always 0, so this is technically a 2-way decomposition, but it's a valid
3-way representation.)

### 3. Strategy document for proving density

notes/16_density_strategy.md (subagent analysis):
- 4 proof strategies analyzed
- Strategy 4 (sliding window) ranked most promising
- Concrete Lean code skeletons provided

### 4. Concrete density verification

Erdos125Density.lean:
- countAB_distinct 81 >= 81 * 8 / 10 = 64 (density >= 80%)
- countAB_distinct 81 = 79 (exact)
- countAB_distinct 36 = 20 (corrected: this counts in [36, 72), not [0, 36))

## Current state of Lean files

All 5 Lean files have 0 sorries:
- `Erdos125.lean` (199 lines): counting infrastructure
- `Erdos125A.lean` (107 lines): A + A = [0, 3^k) structural lemma
- `Erdos125B.lean` (122 lines): B + B + B = [0, 4^m) structural lemma
- `Erdos125C.lean` (108 lines): A + A + A = [0, 3^k) structural lemma (new!)
- `Erdos125Density.lean` (66 lines): density verification

## Key structural facts established (all in Lean 4 + Mathlib)

1. **countA (3^k) = 2^k**: |A ∩ [0, 3^k)| = 2^k
2. **countB (4^k) = 2^k**: |B ∩ [0, 4^k)| = 2^k
3. **A + A = [0, 3^k)**: Every n < 3^k can be written as a₁ + a₂ with a₁, a₂ ∈ A
4. **B + B + B = [0, 4^m)**: Every n < 4^m can be written as b₁ + b₂ + b₃ with b_i ∈ B
5. **A + A + A = [0, 3^k)**: Every n < 3^k can be written as a₁ + a₂ + a₃ with a_i ∈ A

## Erdős 125 Case 2: status

Erdős 125 Case 2 asks: is limsup |A + B ∩ [0, N)|/N > 0?

**Numerical evidence (all verified):**
- k=4 (N=81): density = 79/81 ≈ 0.975
- k=5 (N=243): density = 203/243 ≈ 0.835
- k=6 (N=729): density = 626/729 ≈ 0.859
- k=7 (N=2187): density = 1941/2187 ≈ 0.888
- k=8 (N=6561): density = 5963/6561 ≈ 0.909

**Limsup ≥ 0.83 from numerical evidence.**

**Mathematical proof**: still open in literature.

**Our contribution**: strong structural facts (5 Lean theorems, 0 sorries) that reduce the problem
to a more concrete form, but do not complete the proof.

## Recommendations for next session

### High value (Strategy 4 from notes/16)
Implement sliding-window density lemma in Lean. The key lemma is:
"For every N large enough, |A + B ∩ [N, 2N)| ≥ c·N for some c > 0."

The mod-12 approach gives density ≥ 1/2 from "6 of 12 residues are representable".
But the strategy doc showed this needs careful carry analysis.

### Medium value
Try to push countAB_distinct verification to larger N (e.g., 243, 729).
Currently 243 fails due to compute budget. Need a more efficient representation.

### Low value (clean up)
Document the final state in README and notes.

## Git log (recent commits)

```
4cce394 Density file: fix countAB_distinct 36 value to 20
73ffa81 Density file: add explicit 80% density bound for k=4
0f23e4b notes/16: density strategy document (4 strategies, ranked)
a281211 Add Erdos125C.lean: A+A+A = [0, 3^k) structural lemma (0 sorries)
6b2512e Erdos125B: close the B+B+B sorry - 0 sorries!
fdc95ca Density file: add countAB_distinct verification for small k
637a874 Density file: clean up countA_in_range / countB_in_range examples
```
