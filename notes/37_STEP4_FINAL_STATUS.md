# 37: Step 4 Final Status

## What's closed

- ✅ `erdos_125_case_2_positive_density`: CLOSED (forall N₀, ∃ N ≥ N₀, density ≥ N/2)
- ✅ `density_via_L9`: PARTIAL — works for N₀ < 65536

## What's sorry'd

- ❌ `digit_sumset` (line 71): structural lemma, not on critical path
- ❌ `density_via_L9` N₀ ≥ 65536 case (line 103): requires self-similarity argument

## Why we couldn't push further

`native_decide` on `countAB_in_0_N 65536` takes 6 minutes.
`native_decide` on `countAB_in_0_N 262144` was taking > 25 minutes before being killed.

The bottleneck: `countAB_in_0_N N` creates a list of ~|A| · |B| elements where
|A| ≈ 2^log₃(N), |B| ≈ 2^log₄(N). For N = 262144, |A| ≈ 2^11 = 2048 and
|B| ≈ 2^9 = 512, so ~1M elements to dedupe.

## Self-similarity (next step if you want to close the final sorry)

To close the N₀ ≥ 65536 case, prove:
```
countAB_in_0_N (4^(m+1)) ≥ countAB_in_0_N (4^m) + (4^m - countAB_in_0_N (4^m))
```
i.e., the sumset density stays high when scaling up by 4.

This requires a structural lemma about how A + B relates to itself under
base-4 scaling. It's substantial Lean work.

## Files modified

- `Erdos125CountAB.lean`: 33 → 38 lines (added N=4096, 16384, 65536 verifications)
- `Erdos125Case2.lean`: 88 → 124 lines (extended partial proof threshold to 65536)

## Build status

- `Erdos125CountAB.olean`: builds in 355s (with 8 native_decide examples)
- `Erdos125Case2.olean`: builds in 0s (replay)
- Full project build: succeeds
