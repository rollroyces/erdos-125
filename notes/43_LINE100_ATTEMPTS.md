# 43: Attempts to close line 100 — None Successful

## What I tried

### Option A1: Structural doubling lemma `countAB(4N) ≥ 2 countAB(N)`

- Subagent discovered `countA_3mul_eq_2mul` and `countB_4mul_eq_2mul` (A doubles at scale 3, B doubles at scale 4).
- Attempted to prove `countAB(2N) ≥ countA(N) · countB(N)` (trivial structural).
  - This gives density ≥ `countA(N) · countB(N) / (2N)` at scale `2N`.
  - For `N = 4^m`: `countAB(2 · 4^m) ≥ 2^m · 2^m = 4^m = (2 · 4^m) / 2`. ✓
  - BUT: `density_via_L9` needs `countAB(4^m) ≥ 4^m / 2` directly. Monotonicity gives wrong direction.

### Option A2: Direct `native_decide` for `countAB(4^9) = countAB(262144)`

- Tried twice (once today, once before).
- Both times Lean took >30 min without completing.
- Killed both attempts.

### Option B: Closing `digit_sumset` (line 71)

- Off the critical path for the main theorem.
- Requires substantial mixed-base decomposition infrastructure.

## Why structural proof is hard

The doubling `countAB(4N) ≥ 2 countAB(N)` requires:
- For each `s = a + b ∈ A + B ∩ [0, N)`, we need 2 distinct sums in `[0, 4N)`.
- The naive candidate `s' = 3a + b` works: `3a ∈ A, b ∈ B, 3a + b < 3N + N = 4N`.
- But distinctness: `(a_1, b_1) ↦ 3a_1 + b_1` may collide across different pairs.
  - `3a_1 + b_1 = 3a_2 + b_2` iff `3(a_1 - a_2) = b_2 - b_1`. With `|b_2 - b_1| < N` and `|a_1 - a_2| < N`, this has many solutions.

## Current state

- **2 active sorries**: `Erdos125Case2.lean:71 digit_sumset`, `Erdos125Case2.lean:100 density_via_L9` N₀ ≥ 65536.
- `Erdos125A.lean`: 0 active sorries.
- Full project builds (8866 jobs).
- Latest commit: `95f3489` on `origin/main`.

## Recommended next steps (in order of value)

1. **Formalize `countAB_in_0_N` via `Finset` or `Multiset`** to enable structural proof of `countAB(N) ≥ countA(N/2) · countB(N/2)`. Then apply `countA_3mul_eq_2mul` iteratively.
2. **Prove `digit_sumset`** using Erdős 1955's mixed-base argument. Substantial but tractable.
3. **Accept line 100 sorry** as a known limitation.

## Honest assessment

Closing line 100 cleanly requires either:
- Faster `countAB_in_0_N` implementation (blocked by `Array.set` issues in `native_decide`).
- Self-similarity proof (substantial Lean work).
- Mixed-base digit-sumset (substantial Lean work).

Each path is multi-hour work. For pragmatic close: focus on Option 3 first, as it gives a clean alternative to `native_decide`-based density bounds.