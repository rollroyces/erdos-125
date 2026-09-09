# 38: Step 4 Closing Attempts — Inconclusive

## Goal

Close the 2 remaining sorries in `Erdos125Case2.lean`:
1. `digit_sumset` (line 71)
2. `density_via_L9` N₀ ≥ 65536 case (line 103)

## What I tried

### Attempt 1: Close `decomp_a1_aux_inA` via `inA_mul_three`

Hypothesis: `inA (3 * n) = true` whenever `inA n = true`. This would let us
inductively prove `decomp_a1_aux n k = 3^k * m ∈ A` for `m ∈ A`.

**What worked**:
- `unfold inA` correctly unfolds the recursive definition on `3 * 0`.
- `omega` proves the modular arithmetic: `(3 * n) % 3 = 0` and `(3 * n) / 3 = n`.

**What failed**:
- `rw [inA]` on `inA (3 * (n' + 1))` fails because Lean's equation lemmas for
  dependent pattern matching don't auto-unfold on symbolic arguments.
- `rfl` doesn't unify `inA (m + 1)` with the explicit if-then-else form.
- `native_decide` fails on symbolic arguments.

**Conclusion**: The proof is correct in mathematical content but requires
careful equation-lemma handling that I couldn't get to work in reasonable time.

### Attempt 2: Self-similarity for N₀ ≥ 65536

The 65536 case takes 6 minutes via `native_decide`. The 262144 case takes
> 25 minutes and was killed. Pushing further is computationally infeasible.

**Alternative**: Prove `countAB_in_0_N (4^(m+1)) ≥ 2 · countAB_in_0_N (4^m)`.
This requires structural lemma about how A + B behaves under base-4 scaling.
Not attempted — too complex for one session.

## Final state

No progress on closing the 2 sorries. State is back to:
- `erdos_125_case_2_positive_density` ✅ CLOSED (for N₀ < 65536)
- 2 active sorries in `Erdos125Case2.lean` (lines 71, 103)
- 2 pre-existing sorries in `Erdos125A.lean` (lines 130, 134)

All pushed to `origin/main` (commit `c124288`).
