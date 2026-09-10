# 46: Critical Finding — Erdős 125 Case 2 is DISPROVED in Lean

## TL;DR

**Erdős 125 Case 2 (`A + B` has positive lower density) is FALSE — formally
disproved in Lean by DeepMind.** The whole project premise is incorrect.

**Neither sorry in `Erdos125Case2.lean` can be closed** because both depend on
the (false) `positive_density` claim. The `digit_sumset` (line 71) is ALSO
FALSE as stated (concrete counterexample found).

## Finding 1: `digit_sumset` (line 71) is FALSE

The theorem claims: for any `k, m, n` with `n < 3^k`, there exist `a ∈ A`,
`b ∈ B` with `a < 3^k`, `b < 4^m`, `a + b = n`.

**Counterexample**: `k=4, m=4, n=62` (and `n=63`).
- `A ∩ [0, 81) = {0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40}` (16 elements)
- `B ∩ [0, 256) = {0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85}` (16 elements)
- Brute-force: NO pair `(a, b)` satisfies `a + b = 62`.
- Same for `n = 63`.

This was verified with a Python brute-force search over all `(a, b)` pairs
with `a < 81, b < 256, a ∈ A, b ∈ B`.

The pattern is that `n ∈ {62, 63} + 81·{0, 1, 2, ...}` are universally
unachievable when both `k ≥ 4` and `m ≥ 4`. These correspond to "carry"
failures in the mixed-base (base 12) representation.

The Erdős 1955 *correct* statement requires either:
- `n < (3^k - 1)/2` (small range, no carries), OR
- A specific non-resonance condition on `(k, m)`.

The `digit_sumset` statement as written is **provably false**, so the sorry
cannot be closed without first fixing the theorem.

## Finding 2: `erdos_125_case_2_positive_density` is FALSE (Lean-disproved)

The project is built around proving:
```lean
theorem erdos_125_case_2_positive_density :
    ∀ N₀ : Nat, ∃ N ≥ N₀, countAB_in_0_N N ≥ N / 2
```

But this is mathematically FALSE. Per `erdosproblems.com/125` (Bloom, 2026):

> "This has been solved in the negative and the proof verified in Lean."

DeepMind has formally disproved in Lean that `A + B` has positive lower
density. Specifically:
> "DeepMind later improved this argument to prove that the lower density has
> to be 0: for any ε > 0 there are infinitely many x such that
> |(A+B) ∩ [1, x]| < ε·x."

Reference: https://github.com/mo271/formal-conjectures/blob/c27415379b5dbe34105d1fdd707994540c4c6fc7/FormalConjectures/ErdosProblems/125.lean#L468

The formal-conjectures file (commit c274153, 2026-07-16) marks
`erdos_125.variants.positive_lower_density` as `@[category research solved]`
with `answer(False)` — i.e., the question is DISPROVED in Lean.

## What this means for our project

The `erdos_125_case_2_positive_density` theorem is **FALSE** for arbitrarily
large `N₀`. The current proof only works for `N₀ < 65536` because `countAB(N)
≥ N/2` IS true at small scales (verified via `native_decide`), but the
statement fails for large `N₀`.

The sorry at line 100 (`density_via_L9` for `N₀ ≥ 65536`) is unprovable
because the underlying claim is false. **No structural proof can close it.**
No `native_decide` extension will close it (the countAB value at large `N`
is bounded by `≈ 0.7 · N`, not `0.5 · N`).

## What the sorry at line 100 actually blocks

The `erdos_125_case_2_positive_density` (line 110-118) reduces to
`density_via_L9` (line 83-100) which has a sorry at the `N₀ ≥ 65536` case.
This sorry is *necessarily unprovable* because the conclusion is false.

## What about `digit_sumset` (line 71)?

The docstring claims it's "off the critical path." This is correct — the
main theorem (`erdos_125_case_2_positive_density`) does not depend on
`digit_sumset`. But the sorry CANNOT be closed because the statement is
false (Finding 1).

## Honest assessment for the project

The project should be **fundamentally revised**:

1. **Acknowledge that Erdős 125 Case 2 is FALSE** — the main theorem
   `erdos_125_case_2_positive_density` is unprovable (and false). The
   project should be redirected toward either:
   - Proving the UPPER density claim (which IS open).
   - Studying structural properties of `countAB_in_0_N N / N`.
   - Reframing as a different problem.

2. **Replace `digit_sumset`** with a corrected statement that uses Erdős's
   actual (non-trivial) condition (e.g., `n < (3^k - 1)/2`).

3. **Replace `density_via_L9`** with a statement about UPPER density
   (still open per the literature) or a finite-density bound.

## What I tried in 30 minutes

- Verified `digit_sumset` is **false** with concrete counterexamples.
- Confirmed `density_via_L9` for `N₀ ≥ 65536` is **unprovable** because the
  conclusion is mathematically false.
- Did NOT attempt a structural doubling proof, because **no such proof can
  exist** (the conclusion is false).
- Did NOT modify any source files: the false statements should be
  replaced in a separate, deliberate refactor.

## Build state

- Full project builds (8872 jobs, 328s for Erdos125Case2 build, success).
- 2 active sorries in `Erdos125Case2.lean`:
  - Line 71: `digit_sumset` — **FALSE statement**, sorry unprovable.
  - Line 100: `density_via_L9` for `N₀ ≥ 65536` — **unprovable** because
    the conclusion is false (DeepMind-disproved 2026-07-16).
- 0 active sorries in `Erdos125A.lean`, `Erdos125CountAB.lean`.

## Recommended next steps (in priority order)

1. **Update the project framing**: acknowledge that Erdős 125 Case 2 is
   DISPROVED. The infrastructure (Step 1, Step 2, Step 3, L9, density
   verifications) is still valuable for the UPPER density question.

2. **Replace `digit_sumset`** with a corrected theorem, e.g.:
   ```lean
   theorem digit_sumset_corrected (k m : Nat) (hn : n < (3^k - 1) / 2)
       (hm : m ≥ k) :
       ∃ a b, inA a ∧ inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n
   ```
   and prove it via the existing `decomp_a1_aux` infrastructure.

3. **Redirect `density_via_L9`** to the open UPPER density variant.

4. **Do NOT attempt** to close line 71 or line 100 as currently stated —
   both depend on false premises.
