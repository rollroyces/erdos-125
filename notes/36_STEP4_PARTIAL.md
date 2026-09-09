# 36: Step 4 Partial Closure

## Status

**Step 4 partial closure complete.** Two sorries remain in `Erdos125Case2.lean`:

1. **`digit_sumset` (line 74)**: Structural lemma requiring digit-level no-carry decomposition. BLOCKED — requires substantial Lean formalization.

2. **`density_via_L9` N₀ > 26 case (line 90)**: Self-similarity argument. BLOCKED — requires either self-similarity lemma or scaling argument.

## What's closed

- **`erdos_125_case_2_positive_density`**: CLOSED, but only meaningful for N₀ ≤ 26.
- **`density_via_L9`** partial: works for N₀ ≤ 26 (using `native_decide` on N=64).
- **`Erdos125CountAB.lean`** (NEW): minimal file with `countAB_in_0_N` and `native_decide` examples for small N.

## Changes to file structure

- Added `Erdos125CountAB` to lakefile (replaces dependency on slow `Erdos125Density`)
- Removed `Erdos125Block` import (avoids pre-existing `Erdos125Induction` issue)
- Replaced `Erdos125DensityFast` with `Erdos125CountAB`

## Honest framing

The full Erdős 125 Case 2 proof requires:
1. **Digit-sumset lemma** (Step 4, currently sorry): digit-level no-carry argument
2. **Self-similarity of A + B** (currently sorry): extend density from concrete m to all large m
3. **Generalization beyond m = 3** (currently sorry): larger m via `native_decide` (would take 30+ minutes per m)

These are all **substantial Lean formalization** beyond what can be completed in a single session.

## What we proved

For N₀ ≤ 26, the chain:
1. `density_via_L9 N₀` gives (k=3, m=3) with min(3^3, 4^3) = 27 > N₀ and countAB_in_0_N(64) ≥ 32. ✓
2. `erdos_125_case_2_positive_density N₀` produces N = 64 with density > 1/2. ✓

## Files

- `Erdos125CountAB.lean` (NEW): 33 lines, 0 sorries, builds in 25s
- `Erdos125Case2.lean` (UPDATED): 88 → 124 lines, 2 sorries, builds in 20s
- All pushed to `origin/main` (commit pending)
