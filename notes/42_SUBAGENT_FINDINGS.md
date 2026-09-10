# 42: Subagent Findings — countA_3mul_eq_2mul and countB_4mul_eq_2mul

## Subagent discovery

The subagent identified that `Erdos125.lean` contains powerful **doubling lemmas** for the count functions:

```
countA (3 * N) = 2 * countA N
countB (4 * N) = 2 * countB N
```

These are CLOSED (lines 105, 131).

## Implications

These lemmas say:
- `|A ∩ [0, 3N)| = 2 · |A ∩ [0, N)|`
- `|B ∩ [0, 4N)| = 2 · |B ∩ [0, N)|`

The intuition: A's elements at scale 3N come from "doubling" A's elements at scale N by either using the element as-is or shifting it left by 1 base-3 digit (multiplying by 3). Same for B at scale 4N.

## Why these don't immediately close line 100

For `countAB_in_0_N (4N) ≥ 2 countAB_in_0_N (N)`, we need a similar self-similarity argument for the **sumset**. This is more subtle because:

1. **Cross-terms**: `A ∩ [0, 4N)` includes elements from `A ∩ [0, N)`, `3·A ∩ [0, 4N)`, etc. These interact with `B ∩ [0, 4N)` in complex ways.

2. **Distinctness of `3a + b` representations**: For `(a_1, b_1) ≠ (a_2, b_2)` with `a_i > 0, a_i + b_i < N`, can `3a_1 + b_1 = 3a_2 + b_2`? Yes, this happens when `3(a_1 - a_2) = b_2 - b_1`. So collisions are possible.

3. **Bound**: `3a + b < 3N + N = 4N` ✓, so `3a + b ∈ A + B ∩ [0, 4N)`. ✓

## What we can prove (cleanly)

A **loose** version: `countAB_in_0_N (4N) ≥ countB(N) + countAB_in_0_N (N)`. This holds because:
- For each `s = a + b` with `a > 0`, `3a + b ∈ A + B ∩ [0, 4N)` and `3a + b > s`.
- So `countAB_in_0_N (4N) ≥ countAB_in_0_N (N) + (# pairs with a > 0)` — but this depends on injectivity.

A **tighter** version: `countAB_in_0_N (4N) ≥ 2 · countAB_in_0_N (N) - countB(N)` (off by countB(N) due to `a = 0` case). For density > 1/2 starting from N = 4^8:
- `countAB(4^8) = 51859`, `countB(4^8) = 2^8 = 256`.
- `countAB(4^9) ≥ 2·51859 - 256 = 103462`. We need `4^9/2 = 131072`. So 103462 < 131072 — **NOT enough**.

So even the tighter version is insufficient for the density > 1/2 bound.

## What's actually needed

We need `countAB_in_0_N (4N) ≥ 2 · countAB_in_0_N (N)` (no subtraction). To prove this, we need an additional argument beyond the simple `3a + b` mapping. Possible:

1. **Both `3a + b` AND `a + 4b`**: For `s = a + b` with both `a > 0` AND `b > 0`, we get 2 distinct sums in `[0, 4N)`. But `4b ∈ B` requires `b` such that the base-4 digits of `b` are ≤ 1 — yes, that's the B definition. So `4b ∈ B`. And `a + 4b < N + 4N = 5N` — hmm, not quite `< 4N`. So `a + 4b ∈ [0, 5N)` not `[0, 4N)`.

2. **Use a more clever bijection** to show that the set `{3a + b : a > 0, a + b < N, a ∈ A, b ∈ B}` has size ≥ countAB(N) (which requires showing the map is essentially bijective onto a subset of `[N, 4N)`).

## Status

The structural doubling for `countAB` remains open. The line 100 sorry requires either:
- A careful injectivity proof (subtle)
- A larger `native_decide` (computationally expensive)
- A different structural argument (e.g., digit-sumset closure)

## Commit

This turn's commit (`360f1c5`) was for `decomp_a1_sum` closure. No new commits for the subagent's findings (they only read code, didn't write any).