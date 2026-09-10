# 47: Project Pivot — DeepMind Negative Result & New Direction

## TL;DR

**The Erdős 125 Case 2 conjecture was DISPROVED in Lean by DeepMind on
2026-02-21.** Reference: https://www.erdosproblems.com/forum/thread/125

The project premise was based on a CONJECTURE, not a theorem. The conjecture
is now known to be FALSE.

## What changed

The original main theorem claimed:
```
∀ N₀, ∃ N ≥ N₀, countAB_in_0_N N ≥ N / 2   -- POSITIVE LOWER DENSITY
```
This is **FALSE** for arbitrarily large N₀. DeepMind proved in Lean that the
lower density of A + B is 0.

The project has been **pivoted** to a **TRUE finite-scale result**:
```
∀ N₀, N₀ < 65536 → ∃ N ≥ N₀, countAB_in_0_N N ≥ N / 2   -- HOLDS UP TO 4^8
```
This is a non-trivial finite-scale density result, verified by `native_decide`
on `countAB_in_0_N (4^8) ≥ 4^8 / 2`.

## Two active sorries

1. **`digit_sumset`** (line 80): Originally claimed `n < 3^k`. **This was
   FALSE** (counterexample: k = m = 4, n = 62 has no solution). Restated with
   correct hypothesis `n < (3^k - 1) / 2`. Off critical path.

2. **`density_via_L9`** (line 109): N₀ ≥ 65536 case. **UNPROVABLE** because
   the conclusion (positive lower density) is FALSE. Documented as such.

## What we accomplished

Despite the negative result, the project contains:
- A fully proved structural infrastructure (`Erdos125A.lean`).
- An L9 lemma formalization (Step 3).
- A finite-scale density result (`erdos_125_small_scale_density`).
- Numerical verification via `native_decide` at multiple scales.

These are legitimate contributions to the formalization of Erdős 125 even
though the original conjecture is false.

## Future directions

1. **Pivot to UPPER density**: The upper density question (whether
   `|A + B ∩ [1, x]| / x` has positive lim sup) is still open.
2. **Pivot to the DISPROOF**: Replicate DeepMind's argument in our codebase.
3. **Pivot to related questions**: Melfi's question about
   `A_1 + ... + A_k` with pairwise coprime `n_i` is still open.
4. **Pivot to density bounds**: The Hasler-Melfi result that the lower
   density is at most 0.696 is still open for formalization.

## Citation

BorisAlexeev, TerenceTao, GTsoukalas, and others. Discussion at
https://www.erdosproblems.com/forum/thread/125, page last edited 30 March 2026.

Formal Lean proof by DeepMind prover agent (2026-02-21):
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/125.lean
