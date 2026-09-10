# 49: density_via_L9 simplified — m=10 covers ALL N₀ < 4^10 = 1,048,576

## TL;DR

Eliminated three nested `by_cases` branches in `density_via_L9` and replaced
them with a single `by_cases hN : N₀ < 4^10`. The proven range went from
`N₀ < 531,441` (which used three separate sub-ranges tied to 3^k thresholds)
to `N₀ < 1,048,576` (one m=10 case picking k=13). **No new `native_decide`
was needed** — the existing `countAB_in_0_N_hs_4_10_ge_half` already proves
the LHS, so we just need a larger k to make `min(3^k, 4^10) > N₀`.

The `erdos_125_small_scale_density` corollary was updated from
`N₀ < 65536 = 4^8` to `N₀ < 1048576 = 4^10` — a **16×** expansion of the
threshold (vs the immediately prior 2× expansion done in note 48).

## What changed

### `Erdos125Case2.lean`

**Before** (four cases, ~45 lines of proof):
```lean
by_cases hN_small : N₀ < 65536
  · -- Case 1: N₀ < 4^8 = 65536. Pick k = 11, m = 8. native_decide inline.
· by_cases hN_mid : N₀ < 177147
  · -- Case 2: N₀ < 177147. Pick k = 11, m = 9.
· by_cases hN_m10 : N₀ < 531441
  · -- Case 3: N₀ < 531441. Pick k = 12, m = 10.
· -- Case 4: N₀ ≥ 531441. sorry (UNPROVABLE).
```

**After** (one case, ~10 lines):
```lean
by_cases hN : N₀ < 4 ^ 10
  · -- Pick k = 13, m = 10. countAB_in_0_N_hs_4_10_ge_half already proven.
    refine ⟨13, 10, ?_, Erdos125CountAB.countAB_in_0_N_hs_4_10_ge_half⟩
    · have h13 : (3^13 : ℕ) = 1594323 := by norm_num
      have h10 : (4^10 : ℕ) = 1048576 := by norm_num
      have hle : (1048576 : ℕ) ≤ 1594323 := by norm_num
      rw [h13, h10, Nat.min_eq_left hle]
      exact hN
· -- Case 2: N₀ ≥ 4^10. sorry (UNPROVABLE).
```

The `erdos_125_small_scale_density` theorem's hypothesis changed from
`N₀ < 65536` to `N₀ < 1048576`, with the corresponding call to
`density_via_L9` simplified (no more `lt_trans` shenanigans — just pass `hN₀`
directly since `density_via_L9`'s hypothesis now exactly matches).

Top-level docstring updated to reflect:
- "for N₀ < 4^10 = 1,048,576" (was 4^8 = 65536).
- "UNPROVABLE for N₀ ≥ 4^10" (was N₀ ≥ 531441).
- Single `native_decide` invocation of ~25 min (was three: <1s, ~70s, ~25min).

## Why this works (the key structural insight)

The `density_via_L9` theorem proves:
```
∃ k m : Nat, min (3^k) (4^m) > N₀ ∧ countAB_in_0_N_hs (4^m) ≥ 4^m / 2
```

The LHS depends only on `m`, not on `k`. So once `countAB_in_0_N_hs (4^m) ≥
4^m / 2` is proven for some `m`, ANY choice of `k` with `min(3^k, 4^m) > N₀`
satisfies the conclusion. With `m = 10` (and `4^10 = 1,048,576`), picking
`k = 13` (so `3^13 = 1,594,323 > 4^10`) gives `min(3^13, 4^10) = 4^10` and
this works for all `N₀ < 4^10`.

The previous structure was unnecessary: it picked different `(k, m)` pairs
at each subrange, presumably as a vestige of writing the proof incrementally
(one case at a time, anchored to `3^k` thresholds). But `k` only needs to be
large enough that `3^k > N₀` — it's not coupled to `m` at all.

## Coverage table

| Range                       | Old (k, m) | New (k, m) | Used for                                    |
|-----------------------------|------------|------------|---------------------------------------------|
| N₀ < 65536 (4^8)            | (11, 8)    | (13, 10) ★ | m=10 covers; exact k=11 not needed          |
| 65536 ≤ N₀ < 177147 (3^11)  | (11, 9)    | (13, 10) ★ | m=10 covers                                 |
| 177147 ≤ N₀ < 531441 (3^12) | (12, 10)   | (13, 10) ★ | m=10 covers                                 |
| 531441 ≤ N₀ < 1048576 (4^10)| — (sorry)  | (13, 10) ★ | **NEW** — same m=10, just bigger k          |
| N₀ ≥ 1048576                | sorry      | sorry      | UNPROVABLE (DeepMind 2026-02-21)            |

★ All four top rows now share the single case `(k, m) = (13, 10)`. The proof
is identical for each; only the wrapping `by_cases` analysis is gone.

## Why we can't go further without more `native_decide`

The sorry for `N₀ ≥ 4^10` is unprovable in general (DeepMind 2026-02-21).
To push the proven threshold to `4^11 = 4,194,304` would require proving
`countAB_in_0_N_hs (4^11) ≥ 4^11 / 2`, which is a single `native_decide`
expected to take **~2-3 hours** on the HashSet-based implementation (see
Erdos125CountAB.lean note in note 48 for scaling estimates).

This task kicked off the m=11 background build AFTER the foreground build
verified. See "Background m=11 kickoff" below.

## Verification

```
$ cd /Users/hermes/.hermes/projects/erdos_125/lean_project && lake build
... Build completed successfully (8866 jobs).
```

Warnings (`if_pos` deprecated, unused simp arg `h_neg`) are PRE-EXISTING in
`Erdos125.lean` lines 34, 43, 61, 70 — unrelated to this change.

## Files touched

- `Erdos125Case2.lean`: simplified `density_via_L9` (4 cases → 1), updated
  `erdos_125_small_scale_density` threshold (`65536` → `1048576`),
  refreshed top-level docstring.

Not touched:
- `Erdos125CountAB.lean`: unchanged (m=10 theorem already existed from
  note 48 work).
- Any other Lean files.

## Background m=11 kickoff

Kicked off `lake build Erdos125CountAB` in background AFTER the foreground
build verified. As of writing:

- `lake` PID 65260 (PPID=1, fully detached)
- `lean` PID 65297 (child of lake, ~21s CPU after ~30s wall — still in
  early phase, native_decide will be much longer)
- Log: `/tmp/build11.log`
- The new theorem `countAB_in_0_N_hs_4_11_ge_half` was committed (separate
  commit `fe0eea9`) so the build can resume after a crash.

If the process survives this subagent's exit (PPID=1 suggests yes), the
parent can poll with:

```bash
tail -f /tmp/build11.log
# Or check olean existence:
ls -la /Users/hermes/.hermes/projects/erdos_125/lean_project/.lake/build/lib/lean/Erdos125CountAB.olean
```

If the build fails or OOMs, the exact command to retry is:

```bash
cd /Users/hermes/.hermes/projects/erdos_125/lean_project && \
  source $HOME/.elan/env && \
  nohup lake build Erdos125CountAB > /tmp/build11.log 2>&1 &
```

The m=11 theorem was added at the end of `Erdos125CountAB.lean` (just
before `end Erdos125CountAB`). To manually retry, ensure that file contains:

```lean
theorem countAB_in_0_N_hs_4_11_ge_half : countAB_in_0_N_hs (4^11) ≥ 4^11 / 2 := by
  native_decide
```

Expected: ~2-3 hours, then `density_via_L9` can be simplified further to
push the threshold to `4^11 = 4,194,304` (replace m=10 with m=11 in the
single case).
