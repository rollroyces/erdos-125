# 44: Structural Lower Bound — Status and Honest Limits

## What I built

Added `countAB_lower_bound` theorem to `Erdos125CountAB.lean`:

```lean
theorem countAB_lower_bound (N : Nat) :
    countAB_in_0_N (2 * N) ≥ countA N * countB N := by sorry
```

This is **structurally true** but **not yet proved**. The proof requires reasoning
about `List.concat` + `eraseDups.length` which is non-trivial Lean work.

## What I also built

Added `countAB_in_0_N_fast`: an O(N · |A| · |B|) implementation using `List.foldl`
and `acc ++ [(i, found)]`. Verified equivalent to `countAB_in_0_N` for small N (up to 4096).

**Honest note**: native_decide on `countAB_in_0_N_fast 262144` was attempted twice
and killed after >15 min each time without completing. So the fast version doesn't
actually fix the line 100 closure issue.

## Why line 100 still has a sorry

`density_via_L9` needs: ∃ m ≥ some value with `countAB_in_0_N (4^m) ≥ 4^m/2`.
We've verified this for `m ≤ 8` (i.e., `4^8 = 65536`).
For `m ≥ 9`, we need `countAB_in_0_N (4^m) ≥ 4^m/2`.

The naive structural approach (`countAB(2N) ≥ countA(N) · countB(N)`) gives us
`countAB(2·4^m) ≥ 4^m` but NOT `countAB(4^m) ≥ 4^m/2` — monotonicity gives the
wrong direction.

The doubling lemma `countAB(4N) ≥ 2 countAB(N)` would close it, but requires:
- Map `(a, b) ↦ 3a + b` from `A ∩ [0, N) × B ∩ [0, N)` to `A + B ∩ [0, 4N)`.
- Map is INJECTIVE on the relevant subset — this is the hard part.
- Collisions: `3a + b = 3a' + b'` when `3(a - a') = b' - b`. Not always distinct.

## What's actually proved

- `countA_3mul_eq_2mul`: A doubles when multiplied by 3. ✓ (in Erdos125.lean)
- `countB_4mul_eq_2mul`: B doubles when multiplied by 4. ✓ (in Erdos125.lean)
- `countA_3pow_eq_2pow`: countA(3^k) = 2^k. ✓
- `countB_4pow_eq_2pow`: countB(4^k) = 2^k. ✓
- `countAB_in_0_N N ≥ N/2` for N ∈ {4, 16, 64, 256, 1024, 4096, 16384, 65536}. ✓ (verified by native_decide)
- `countAB_in_0_N_fast` equivalent to `countAB_in_0_N` for small N. ✓

## What's still BLOCKED

- `digit_sumset` (Erdos125Case2.lean:71) — off critical path
- `density_via_L9` (Erdos125Case2.lean:100) — N₀ ≥ 65536 case
- `countAB_lower_bound` (Erdos125CountAB.lean) — structural lemma, sorry

## Current state

- **3 active sorries**: digit_sumset, density_via_L9 line 100, countAB_lower_bound.
- `Erdos125A.lean`: 0 sorries ✅
- Full project builds (8866 jobs) ✅
- Latest commit: `60f6d27` on `origin/main`

## Recommended next steps

1. **Prove `countAB_lower_bound`** using induction on List structure with
   `List.length_append`, `List.length_filter`, and `Nat.le_trans`. Should take
   1-2 hours of Lean work.
2. **Prove `countAB(4N) ≥ 2 countAB(N)` doubling** — needs injectivity argument
   for `(a, b) ↦ 3a + b`. Substantial.
3. **Use Erdős 1955's mixed-radix digit-sumset** — biggest payoff, hardest work.
