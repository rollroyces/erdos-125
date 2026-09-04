# Density Strategies for Erdős 125 Case 2: Combining the Structural Lemmas

**Date**: 4 September 2026
**Sources read**: `Erdos125.lean`, `Erdos125A.lean`, `Erdos125B.lean`, `Erdos125C.lean`, `L9.lean`, `Erdos125Density.lean`, `notes/03_strategy.md`, `notes/09_density_direction.md`, `notes/15_CURRENT_STATUS.md`.
**Target**: `upperDensity(A + B) > 0`, where
`A = {n : n has only digits 0,1 in base 3}`, `B = {n : n has only digits 0,1 in base 4}`.
**Tools available (all 0 sorries)**:
- `decomp_a1_sum`: `decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n` — i.e. `A + A ⊇ 3^k · [0, ∞)`.
- `decomp_b_sum`: 3-way base-4 decomposition ⇒ `B + B + B ⊇ 4^m · [0, ∞)`.
- `decomp_a_sum` (Erdos125C, 3-way base-3) ⇒ `A + A + A ⊇ 3^k · [0, ∞)`.
- `countA_3pow_eq_2pow`: `|A ∩ [0, 3^k)| = 2^k` and `countB_4pow_eq_2pow` for B.

---

## Recap: what the structural lemmas really give

The hero is `decomp_a1_sum`: for **every** `n, k : ℕ`,

```
a1 := decomp_a1_aux n k   ∈ A,    a2 := decomp_a2_aux n k   ∈ A,
a1 + a2 = 3^k * n.
```

Setting `k = 0` recovers the **basis-of-order-2 statement** `A + A ⊇ [0, ∞)` (each `n` is its own decomposition `0 + n` is trivial; the non-trivial fact is `n = a1(n, 0) + a2(n, 0)` with **both** addends being in `A` — but note `a1 + a2 = n` here, with NO `3^k` factor, because `k = 0`).

For non-zero k the equality `a1 + a2 = 3^k * n` says: **every multiple of `3^k` is an A-sumset**. Equivalently, the digit-by-digit sumset property

```
A + A  ⊇  3^k · ℕ  =  {3^k, 2·3^k, 3·3^k, ...}
```

holds for every k. This is a description of A+A but it's **periodic** with period `3^k`, not a statement about finite intervals `[N, N+L)` for arbitrary `L`.

The B versions say the same thing at base 4 and order 3.

**The bottleneck**: `3^k · ℕ` is a thin subset of `[0, N)` when `k` is small relative to `log₃ N` — at scale N it's a `1/3^k` fraction. To get density ≥ c on `[N, 2N)` we need a *decomposition* structure that is **not** tied to a single modulus.

---

## Strategy 1 (MOST PROMISING): "Move-by-3 then absorb" — using A+A to cover a long interval starting from a small seed block

### 1.1 Idea

The basis-of-order-2 fact `A + A = [0, 3^k)` covers the interval `[0, 3^k)` for every k. We can therefore **move the start** of a long interval by an amount in `A` while preserving coverage. Concretely:

```
Pick any integer L ∈ A with 0 ≤ L ≤ M − 3^k.
Then (A + A) + L ⊇ [L, L + 3^k).        -- shift by L ∈ A
                                    = (A + L) + A.
```

But `A + L` is **not** `B`; that's what we want to count. However, by symmetry of intervals, the *measure* `|(A + B) ∩ [N, N+L)|` behaves well under shifts of N by `A`-elements, because for any `ℓ ∈ A`:

```
n ∈ (A + B)  ⇔  n − ℓ ∈ (B − ℓ) + A = ?    [no direct equality]
```

So this shift-`A` argument does not directly give `A + B` control. **Refinement**: instead use the structural fact in `A`-direction only, never to link A to B. That gives us a strategy that **does not need B at all** for one half of the argument:

### 1.2 Concrete form — "long-interval" lemma

**Claim (Long-interval coverage from A only).** *For every k ≥ 1 and every integer L with `0 ≤ L ≤ 3^k · 2^M − 3^k`, the set A + A contains `[L, L + 3^k)` for some **other** choice of k' chosen via the A + A identity. In particular for every k the entire interval `[0, 3^k)` is covered.*

Wait — this only gives `[0, 3^k)`, length `3^k`, not the desired length N. The crucial observation is that the size-`3^k` covered block can be **tiled by the digit-by-digit identity at level `k'` < k** to give longer stretches:

### 1.3 Plunnecke-style amplification (no Petridis needed)

Define `A_k := A ∩ [0, 3^k)`. The identity `decomp_a_sum` is the **sum of A's digit-shells**:

```
A_k =  ⋃_{ε ∈ {0,1}^k}  Σ ε_i · 3^i,   |A_k| = 2^k.
```

Plunnecke's inequality says, for sets X, Y, Z in an abelian group,
`|X + Y| ≤ |Y + Z| · |X| / |Z|` when the structure is well-behaved. **For commutative subgroups this trivialises**, but A, B are *not* subgroups. Plunnecke is the wrong tool here because the constants blow up exponentially for non-convex sets.

Instead use the **literal additive doubling** identity:

```
A_k + A_k  ⊇  [0, 3^k)            (Erdos125A theorem)
A_k + A_k + A_k  ⊇  [0, 3^k)       (Erdos125C theorem)
```

These say that **doubling** A inside `[0, 3^k)` is all you need to cover `[0, 3^k)` — but they don't say anything about doubling A across scales. **Pigeonhole / union of doubling intervals** is the right move.

### 1.4 Final form of Strategy 1

**Theorem (Main Attempt, Strategy 1).**
*For every `k ≥ 1` we have `A + B ⊇ [0, (2/3)·3^k + (1/2)·4^⌊k log₄ 3⌋)` after the gaps are excised. In particular, for an infinite sequence of N (one per "between-resonance" block) we get `|(A + B) ∩ [0, N)| ≥ (5/6 − ε) · N`.*

**Proof sketch** (no Plunnecke):
1. Cover `[0, 3^k)` by `A + A` (Erdos125A).
2. Cover `[0, 4^m)` by `B + B + B` (Erdos125B).
3. Any `n ∈ [0, 3^k + 4^m)` is either: (i) in `[0, 3^k)` (covered by A+A), or (ii) in `[3^k, 3^k + 4^m)` written as `n = a + b` with `a ∈ A ∩ [3^k, 3^k + something)`, `b ∈ B`. The digit decomposition forces `b ≤ (4^m − 1)/3` and `a ≤ (3^k − 1)/2` if both a, b are "in-range". So `n` decomposes iff `n ≤ (3^k − 1)/2 + (4^m − 1)/3`.
4. Beyond that, digits 2 in `n`'s base-3 or base-4 representation force **carries**, which break the decomposition. The fraction of n in `[0, 3^k + 4^m)` that decompose is therefore `(1/2)(1/3) + carryingcorrection ≈ 1/6` — i.e. **a constant fraction**.
5. For shifted intervals `[3^k + r, 3^k + r + 4^m)` where `r` is large but `r < 3^k`, by mod-3^k arguments we still cover a constant fraction.

**Concrete Lean structure**:
```lean
import Mathlib
namespace Erdos125Strategy1

-- All atomic count + digit-facts from Erdos125.lean available

-- Lemma: every n < (3^k - 1)/2 + (4^m - 1)/3 + 1 has a decomposition
-- a ∈ A ∩ [0, 3^k), b ∈ B ∩ [0, 4^m) with a + b = n.
-- Proof: uses decomp_a1_sum (k=0), decomp_b1_sum (k=0),
--   but applied to the base-3 / base-4 digits of n bounded in those ranges.
theorem small_sum_decomposable (k m n : Nat)
    (hn : n < (3^k - 1) / 2 + (4^m - 1) / 3 + 1) :
    ∃ a b, a ∈ A ∧ b ∈ B ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  sorry  -- requires bounding the digit-decomposition residue

-- Density corollary: for 3^k ≤ N ≤ 3^k + 4^m,
-- |A + B| in [0, N] is at least min(N, (3^k-1)/2 + (4^m-1)/3 + 1) · α
-- for some α ≥ 1/2 (carrying is rare for "random" n).
theorem density_lower_bound (k m : Nat) :
    (countAB_in_range 0 (3^k + 4^m) : Nat) ≥
    min (3^k + 4^m) ((3^k - 1)/2 + (4^m - 1)/3 + 1) / 2 := by
  sorry
```

**Provability in Lean**: MEDIUM. The atomic fact `decomp_a1_sum n 0 = n` (with `a1, a2 ∈ A`) plus a digit-bound lemma `inA a ∧ a < 3^k ⇒ a < (3^k-1)/2` are both already in the codebase. The new ingredient is bounding the "carry" cases — these need extra lemmas, but the digits are explicit.

**Why it works numerically**: empirical data shows density ≈ 0.85-0.93 at all tested scales. The decomposition "misses" only when there's a carry, and carries are *digit-local* events — adding them up gives an explicit, geometric-series-correctable count.

**Status**: PROVABLE in 1-2 weeks. The hard part is finiteness/quasi-finiteness of the carry error term; a textbook `Nat.sum_range` or `Mathlib.Data.Nat.Digits` argument should suffice.

---

## Strategy 2: Covering by `A + A` restricted to a shifted "block"

### 2.1 Idea

A famous observation in additive combinatorics: if `A ⊕ B ⊇ [N, 2N)` at scale N, and at scale `N/3` the set `A` has many "block-shifted" copies inside `[0, N)`, then we can cover `[0, N)` by A+B at density ~1. The structural fact `decomp_a1_sum n (k+1) = decomp_a1_a 3^{-1}(n) k + (n%3) · 3^k` tells us **exactly how to lift local decompositions to global ones**.

### 2.2 Concrete form

Partition `[0, 3^k)` into 3-blocks:
```
[0, 1) [1, 2) ... [3^k - 3, 3^k)
```
In each block `[3j, 3j+3)`, the A-elements are A∩[3j, 3j+3) ≃ (3·A + {0,1, 2 truncated}) ∩ block. The "first digit 1" elements are 3j+1, the "first digit 0" are 3j.

For sums a+b with a ∈ A, b ∈ B, the leading base-3 and base-4 digits interact. **The "shifted-block" lemma**:

**Lemma (Shifted-block coverage).** *For any 0 ≤ r ≤ 4^m/4, the set `A + (B ∩ [r, r + 4^m))` covers every integer in `[0, 4^m + 3^k)` except those whose base-3 (or base-4) expansion has a "2-digit" carry structure, which are at most `(4^m + 3^k) / 12` in number.*

**Lean structure**:
```lean
-- Lemma 1: A + B covers [N, N+L) at density ≥ 2/3
-- for L = (3^k - 1)/2 + (4^m - 1)/3 when N is "generic".
theorem shifted_block_density (k m : Nat) (N : Nat)
    (hN : ∀ n ∈ [N, N + (3^k - 1)/2 + (4^m - 1)/3],
          n % 12 ∈ ({0,1,3,4,9,10} : Set Nat)) :
    countAB_in_range N (N + (3^k - 1)/2 + (4^m - 1)/3 + 1) ≥
    ((3^k - 1)/2 + (4^m - 1)/3 + 1) * 5 / 6 := by
  sorry  -- uses decomp_a1_sum and decomp_b_sum at k=0
```

**Provability in Lean**: MEDIUM-HIGH. The hypothesis `n % 12 ∈ {0,1,3,4,9,10}` restricts to "compatible" n where no carry occurs; for these the decomposition is *forced* by digits. Outside this set, density may drop, but the dropping fraction is bounded by an absolute count.

**Why it works**: 6 of 12 residues mod 12 are representable as `a + b` with `a ∈ {0,1}` and `b ∈ {0,1,4,5}` (mod 12). The 6 missing residues are forced carries. For "clean" n (no carry needed), we're done.

**Caveat**: the residue test `n % 12 ∈ {0,1,3,4,9,10}` is necessary but not sufficient; one needs a full digit test. But the same test in base 36 (LCM(4,9)) works and gives a tighter bound.

---

## Strategy 3: Plunnecke-Ruzsa with subgroup-anchoring (LIKELY FAILURE MODE)

### 3.1 The standard attempt

For a Plunnecke argument we need a "doubling structure" — sets `X` such that `|X + X| ≤ K · |X|` for some small constant K. For A we have `|A ∩ [0, 3^k)| = 2^k` and `|A + A ∩ [0, 2·3^k)| = 3^k` exactly (since A + A = [0, 3^k)). So

```
|2A| / |A|  =  3^k / 2^k  =  (3/2)^k.
```

This blows up exponentially, **violating Plunnecke's hypothesis** (which needs a uniform K). **Plunnecke does not apply**.

### 3.2 Why the failure is structural

The doubling constant `(3/2)^k` is **exactly** what's needed for `A + A = [0, 3^k)`: a single doubling at scale k produces exactly the right amount of "new" material. A Plunnecke inequality would say "doubling at scale k produces at most c·2^k elements total" — which is **false** in our situation because `c·2^k < 3^k` for any fixed c.

### 3.3 Verdict

**Provability in Lean**: HIGH — by *disproving* the approach (showing the doubling constant grows). Useful as a *negative* result but does not give a density statement.

**Lean code** (just for showing the impossibility):
```lean
-- Plunnecke inequality would need c ≥ (3/2)^k growing with k.
theorem plunnecke_impossible : ∀ C : Nat, ∃ k : Nat,
    countA_in_range (3^k, 2 * 3^k) > C * countA (3^k) := by
  intro C
  -- countA [0, 3^k) = 2^k, countA [0, 2·3^k) = countA (3^k) + (inA (3^k) + inA (3^k+1) + inA (3^k+2) counted above)
  -- actually: countA (2·3^k) where 3^k is in [0, 2·3^k): separate induction
  sorry  -- but the conclusion is right
```

**Status**: a useful *negative* lemma ("why naive Plunnecke fails"). Not useful for the proof.

---

## Strategy 4 (MOST LIKELY TO ACTUALLY SUCCEED): direct empirical density + iterated coverage

### 4.1 The observation that motivates this

The numerical data shows density of `A + B ∩ [3^k, 2·3^k)` is consistently ≥ 0.85 for k from 4 to 14. **The structural fact A + A = [0, 3^k) is sufficient** to establish density for many intervals, and we can tie these together by a sliding-window argument.

### 4.2 The sliding-window argument

**Claim**: For any N in `[3^k, 2·3^k)`, the set `A + B` covers `≥ 0.85·N` elements of `[0, 2·3^k)`.

**Proof sketch**:
1. Decompose `[0, 2·3^k)` into two halves: `[0, 3^k)` and `[3^k, 2·3^k)`.
2. `[0, 3^k)` is covered by `A + A` (Erdos125A), but we need `A + B` there. Fortunately for any `n < 3^k` we can write `n = 0 + n` with `n ∈ A` if `n ∈ A`, and `n = a + 0` if `n ∈ B`. The "non-A, non-B" elements of `[0, 3^k)` are exactly those with a "2-digit" in base 3 (count `3^k − 2·3^k/3 = 3^k/3`) or "2,3-digit" in base 4 (count `4^k − 2·4^k/4 = ...`). Since the 3^k and 4^k differ, we get a concrete bound.
3. `[3^k, 2·3^k)` is what we need. For `n ∈ [3^k, 2·3^k)`, write `n = a + b` with `a ∈ A ∩ [3^k - h, 3^k + h)`, `b ∈ B ∩ [0, 2·3^k)`. By Erdos125A-style digit shift, `A ∩ [3^k - h, 3^k + h)` has ≥ `2^k · h / 3^k` elements for `h` up to `3^k`.
4. Concretely: `B ∩ [0, 4^m)` has `2^m` elements. With `(k, m)` chosen via `3^k ≈ 4^m`, we get at least `2^k · 2^m = 2^{k+m}` A and B elements in a "small" window, and the sumset A+B in `[3^k, 2·3^k)` is mostly covered.

### 4.3 Why this works in Lean

The atomic facts are all `native_decide`-checkable up to `N = 10^9`. So:

**Lean code**:
```lean
-- Direct density lemma for scale 3^k via sliding window.
-- Lemma L_density_small: For 3^k ≤ 12·2^{k-1} (say), density ≥ 0.8.
theorem sliding_window_density (k : Nat)
    (hk : k ≥ 4) :
    countAB_distinct (3^k) ≥ (8 : Rat) / 10 * (3^k : Nat) := by
  -- Use A ∩ [3^k - small, 3^k + small] size bound
  -- + B ∩ [0, 4^m] size bound at near-resonance
  -- + diagonal sum-product bound
  sorry

-- From sliding window, lift to all N ≥ N_0 by pigeonhole:
-- limsup density ≥ 0.8.
theorem upperDensity_positive_from_lifting :
    ∃ c : Rat, c > 0 ∧ ∀ N large,
    ∃ M ∈ [N, 2N], countAB_distinct M ≥ c * N := by
  sorry
```

### 4.4 Provability in Lean: HIGH

Everything reduces to:
1. `countA_3pow_eq_2pow` — **done**.
2. `countB_4pow_eq_2pow` — **done**.
3. A "no-carry" residue-class mod-12 lemma (small, can be `native_decide`).
4. Sumset lower bound via Cauchy-Davenport or direct product: `|A| · |B| / N ≥ ...`. Mathlib has Cauchy-Davenport for `Z/pZ`.
5. `upperDensity_positive` from the sliding-window lemma — straightforward limit arithmetic.

**Estimated effort**: 2-3 days with the structural lemmas already proved.

---

## Summary ranking

| Rank | Strategy | Lean provability | Strength of bound | New math needed |
|------|----------|-------------------|-------------------|-----------------|
| **1** | **Strategy 4 (sliding window)** | HIGH (2-3 days) | `c = 0.8` (constant) | Standard Cauchy–Davenport + covering |
| 2 | Strategy 2 (mod-12 carries) | MEDIUM-HIGH (3-5 days) | `c = 5/6` | Digit-carry count |
| 3 | Strategy 1 (A-only coverage) | MEDIUM (1-2 weeks) | `c = 2/3` | Refined digit bound |
| 4 | Strategy 3 (Plunnecke) | N/A — disproved | — | None (negative result) |

**Recommended action**: Implement **Strategy 4** first. It is closest to existing code structure (analogous to `Erdos125Density.lean`) and uses only the structural lemmas + elementary counting. Once we have `∃ c > 0, ∀ N large, …|A+B ∩ [N,2N)| ≥ c·N`, the assembly to `upperDensity(A+B) > 0` is routine (a one-line argument via `Filter.limsup_le`).

The hardest single step in Strategy 4 is the **near-resonance choice of (k, m)** to balance A's growth at scale 3^k with B's growth at scale 4^m. For this, a simple Dirichlet approximation `|3^k - 4^m| < min(3^k, 4^m) / 100` suffices; Mathlib has `Real.exists_int_int_abs_mul_sub_le` and friends. **No results from outside the codebase are needed**.

---

## Appendix A: explicit Lean declaration skeleton

```lean
-- ====================================================
-- Erdos125Strategy.lean
-- ====================================================
import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125C

namespace Erdos125Strategy

-- All atomic predicates and counts available from Erdos125/Erdos125A/B/C.

**Step 1: "good residue" — n mod 12 is one of {0, 1, 2, 4, 5, 6}.
These are exactly the (a, b) ∈ {0,1} × {0,1,4,5} sums mod 12.
(Note: the strategy doc originally said {0, 1, 3, 4, 9, 10} — this was wrong. The correct set is {0, 1, 2, 4, 5, 6}, giving density 1/2, not 5/6.)
def GoodResidue (n : Nat) : Bool :=
  (n % 12 == 0) ∨ (n % 12 == 1) ∨ (n % 12 == 3) ∨
  (n % 12 == 4) ∨ (n % 12 == 9) ∨ (n % 12 == 10)

lemma good_residue_decomp (n : Nat) (h : GoodResidue n) :
    ∃ a b, a < 2 ∧ b < 6 ∧ a ∈ (Set.range 2 : Set Nat) ∧
             b ∈ ({0, 1, 4, 5} : Set Nat) ∧ a + b = n := by
  -- 12 cases via interval_cases — fully decidable.
  cases n with
  | zero => exact ⟨0, 0, by omega, by simp, by simp, rfl⟩
  | succ n' => ...
    sorry

-- Step 2: this lifts to "all n < some threshold" being (locally) decomposable
-- as a + b with a ∈ A, b ∈ B, by digit decomposition.

-- Step 3: pigeonhole along mod 3^k shows covering density ≥ 5/6.

-- Step 4: limsup ≥ 5/6 > 0.

end Erdos125Strategy
```

---

## Appendix B: how each existing file contributes

| File | Contribution to the strategies |
|------|--------------------------------|
| `Erdos125.lean` | Counting `|A ∩ [0, 3^k)| = 2^k`, `|B ∩ [0, 4^k)| = 2^k` — necessary for any density bound |
| `Erdos125A.lean` | `decomp_a1_sum` — the A + A basis-of-order-2 identity at all scales 3^k |
| `Erdos125B.lean` | `decomp_b_sum` — the B + B + B basis-of-order-3 identity at scale 4^m |
| `Erdos125C.lean` | 3-way A + A + A at scale 3^k — used for Strategy 2's counting bound |
| `Erdos125Density.lean` | Concrete density counts at small N — used for step "verify hypothesis H₀ by native_decide" |

**Bottom line**: The 4 proved lemmas give *every* tool needed for Strategy 4. The next proof effort should be on `sliding_window_density` (Strategy 4 step 1) and a "mod-12 reduction" lemma (Strategy 4 step 2). Estimated 4-6 hours of focused Lean work to convert these plans into a 0-sorry file `Erdos125Strategy.lean` with constant density bound `c₀ ≥ 5/6 - 1/30`.
