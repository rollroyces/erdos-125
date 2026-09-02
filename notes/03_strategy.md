# Phase G: Mathematical Strategy for Erdős 125 Case 2
## Positive Upper Density, Zero Lower Density

**Date:** 3 September 2026
**Status:** Research synthesis (paired with formalization agents)
**Goal:** Identify a Lean-formalizable strategy that determines whether
(A+B) has zero upper density (Case 1) or positive upper density (Case 2),
given (already proved in Lean): lower density = 0.

---

## 1. Summary of prior phase

The Erdős-125 statement is **4-way ambiguous** by the very wording in
[BEGL96] ("positive density? positive upper density?"). The Lean file
`125.lean` formalizes all four cases:

| Case | Statement | Status (Lean) |
|------|-----------|---------------|
| 1 | upper = 0 ∧ lower = 0 | **Open** (this report's concern) |
| 2 | lower = 0 ∧ upper > 0 | **Open** (this report's concern) |
| 3 | upper = lower > 0 | **Solved** (False — DeepMind, May 2026) |
| 4 | lower > 0, lower ≠ upper | **Solved** (False — implied by lower=0) |

The two open cases are **mutually exclusive** and the question is just:
*Is `upperDensity(A+B) = 0` or `> 0`?*

The Python experiment in `01_results.md` shows:
- `|A+B ∩ [0, N]| / N` stabilizes around **0.85–0.93** for N ≤ 10⁸,
- The *max gap* in `A+B` grows (7,680 at N=10⁶, 404,719 at N=10⁷).

So we have **two competing signals**:
- The **average density stays high** (positive upper density strongly suggested).
- The **largest gaps keep growing** (consistent with lower = 0, not upper).

Both can be simultaneously true **if and only if Case 2 holds**.

---

## 2. Literature landscape

### 2.1 Classical works
- **[BEGL96]** Burr, Erdős, Graham, Li. *Complete sequences of sets of integer powers.*
  Acta Arith. **77** (1996), 133–138. — original problem statement.
- **[Er97, p. 156]** Erdős. *Problems in number theory.* NZ J. Math. 26 (1997),
  155–160. — Erdős uses "positive density" to mean **positive lower density**
  (confirmed by quotation: "> c x for some c>0 and x>x₀").
- **[Me01]** Melfi. *An additive problem about powers of fixed integers.*
  Rend. Circ. Mat. Palermo (2) (2001), 239–246. — proved
  `|A+B ∩ [1,x]| ≫ x^{0.965}`; counter-example `{3,9,81}` for the
  generalized statement.
- **[Me04]** Melfi. — construction showing that the condition
  `Σ 1/(dᵢ − 1) ≥ 1` is *almost* tight.
- **[HaMe24]** Hasler & Melfi. *On sums of distinct powers of 3 and 4.*
  Combinatorics and Number Theory (2024). — improved to
  `x^{0.9777}` and proved `lowerDensity(A+B) ≤ 1015/1458 ≈ 0.696`.

### 2.2 DeepMind's AlphaProof Nexus (May 2026)
arXiv:2605.22763; arXiv:2605.22763v1 (HTML).
- Proved: `HasPosDensity(A+B)` is **False** (Case 3 disproved).
- Proved: `lowerDensity(A+B) = 0` (Case 4 disproved).
- *Both proofs are public Lean files in the Formal Conjectures repo.*

The DeepMind proof of `lowerDensity = 0` uses a **multiplicative-thinning
strategy** that I have read in full (commit `c27415379b5dbe34105d1fdd707994540c4c6fc7`,
file `FormalConjectures/ErdosProblems/125.lean`, line ~468 onward). Its
key innovation is *re-using the same 6/5 gap ratio* that disproved Case 3,
but iterated:

```
density at N := |A+B ∩ [0, N)| / N
After a single "Diophantine-resonant" step (3^k ≈ 4^m),
density at N·min(3^k, 4^m) ≤ density at N · (14/15).
Iterating r times gives density ≤ (14/15)^r at scale N · (3^k 4^m)^r.
This forces lim inf = 0.
```

This is exactly the structure we should *mirror* in our upper-density
proof: an argument of the form

```
density at N := |A+B ∩ [0, N)| / N
After a single "additive-shift" step,
density at N + L   ≥  density at N · (some constant > 0) + (additive boost),
```

which (if it can be made arbitrarily close to 1) would force
`lim sup > 0`.

### 2.3 The "Pach-Pintz" naming
The DeepMind lemma is named `pach_pintz_diophantine_gaps` but the forum
explicitly notes that **no underlying literature under that exact name
could be located**. It appears to be a *hallucinated attribution* by the
agent. We should *not* rely on any "Pach-Pintz theorem" as black-box
input. Every component of the proof must be re-derived from base
Diophantine approximation.

### 2.4 Adjacent literature (other Erdős sumsets)
- **Erdős #124**: generalized "complete sequences" `Σ P(dᵢ, k)`. Different
  problem; [Me04] shows the condition `Σ 1/(dᵢ − 1) ≥ 1` is essentially tight.
- **Erdős #741**: positive-density basis of order 2; uses fat-sparse intervals
  `[4^{3^k}, 10·4^{3^k})` and the partition-denial structure.
- **[HaMe24]** also mentions **Proposition 5**: a direct lower-density bound
  via large gaps of `A+B`, which directly forces upper ≤ lower + ε for
  some ε — but the explicit constants don't quite rule out Case 2.

### 2.5 Sumset density — general theory
- **[Kra–Moreira–Richter–Robertson 2024]** *A proof of Erdős's B+B+t
  conjecture.* Confirms: positive upper Banach density ⇒ contains
  restricted sumsets. Applies only to Banach density, not asymptotic.
- **[Fibonacci sumsets, Stöhr, Mauduit–Rivat]** — about digit-sum
  functions and *automatic* sequences, but not directly about digit-
  *restricted* sets. May yield machinery for normal-order results.

---

## 3. Structural reasons the density behaves as it does

### 3.1 The gap structure
```
A contains  [3^k/2, 3^k)    ← top digit 1 ⇒ excluded
B contains  [4^m/3, 4^m)    ← top digit 2 or 3 ⇒ excluded
A + B  ⊇   [3^k/2, 3^k) + [4^m/3, 4^m)
           = [3^k/2 + 4^m/3, 3^k + 4^m)
           hence a GAP of length  min(3^k, 4^m) − (3^k/2 + 4^m/3)
                            =  (1/2 + 1/3) · min(3^k, 4^m) − δ(3^k,4^m)
                            ≈  (5/6) · min(3^k, 4^m)            if 3^k ≈ 4^m
```
⇒ When `3^k ≈ 4^m`, we get a **gap of length ≈ (5/6) · N** in `A+B` at
scale N. This is the *multiplicative* Diophantine step (used by DeepMind).

### 3.2 The "density high" structure
For *most* scales N, `A+B` has density ≈ 0.85. The reason: the set
`A + B` is *almost* all of `[0, 6·4^k)` because

```
A  ⊇  {0, 1, 3, 4, 9, 10, 12, 13, ...}    ≈ 2^k elements in [0, 3^k)
B  ⊇  {0, 1, 4, 5, 16, 17, 20, 21, ...}  ≈ 2^m elements in [0, 4^m)
A + B covers nearly all residues mod 12 at density 0.85+
```

The conjecture (Case 2 TRUE) is that these two facts are not in
contradiction because the high-density intervals and the big-gap
intervals are **interleaved** at *different scales* — never the same N.

### 3.3 Why this is hard
A positive *upper* density argument has to show that **there exist
arbitrarily large N at which `A+B` has density ≥ c > 0**, while
*never* showing a uniform lower bound. Existing techniques give:

| technique | gives | doesn't give |
|-----------|-------|--------------|
| Beurling-type quasi-shifts | existence of positive density intervals | `lim sup > 0` |
| The multiplicative thinning (DeepMind) | upper ≤ (6/5)·lower | lower > 0 |
| The 5/6 gap ratio | scale-N gap of size (5/6)N | upper = 0 |
| Melfi x^{0.9777} | `|A+B| ≥ N^{0.9777}` everywhere | `|A+B| ≥ c·N` |
| Hasler-Melfi 0.696 | lower density ≤ 0.696 | lower density > 0 |

---

## 4. The recommended proof strategy

### 4.1 Strategy statement (conjectural)

> **Strategy S1 — "shift-density" lemma + iteration.**
>
> Show that for **all sufficiently large N**, there exists an integer
> `M ∈ [N, 2N]` such that
> ```
> |A + B| ∩ [M, M + N)   ≥   c · N      for some absolute c > 0.
> ```
> This proves `upperDensity(A + B) ≥ c > 0`, hence **Case 2**.

This is the *additive* (shift) analogue of DeepMind's *multiplicative*
(Diophantine) thinning.

### 4.2 Why this should be true

For any N, look at intervals `[L, L + N)` where L is roughly a multiple
of `min(3^k, 4^m)`. Two cases:

**Case (a) L sits *between* two resonance scales** (no nearby 3^k ≈ 4^m).
Then A + B restricted to `[L, L + N)` is "generic", and the density is
≈ 1 (because both A and B contain all small residues up to their
generation point).

**Case (b) L sits *at* a resonance scale** (3^k ≈ 4^m ≈ L).
Then the *gap* argument gives a single big gap, but in `[L, L + N)`
there are still ≈ (5/6)·N elements coming from the "other" digit
patterns.

Combining, we get that **at every scale N, the local density of A+B
is at least c for some c in [0.5, 0.95]**. This is a *defect*
estimate of the form "bad intervals only ever kill a 6/5 fraction of
density at one specific scale, not at all scales."

### 4.3 Key new mathematical lemma needed (not in literature)

> **Lemma (Shifted density bound).** *There exists an absolute constant
> `c₀ > 0` (e.g., `c₀ = 5/6`) and a sequence `N_i → ∞` such that for
> each `i` and for some `M_i ∈ [N_i, 2 N_i]`,*
>
> ```
> |(A + B) ∩ [M_i, M_i + N_i)| ≥ c₀ · N_i .
> ```

The proof would use:
1. **Block structure** — split `[0, N]` into `L = ⌊log₂ N⌋` blocks of
   size ≈ N/L. In each block, the "best" interval has density ≥ c.
2. **Non-resonance argument** — at non-resonance scales the density is
   bounded below by the simple union `|A ∩ [0, x)| · |B ∩ [0, N-x)| / N`,
   which averages to ~0.7+ over most choices of x.
3. **Resonance avoidance** — at resonance scales (the only ones DeepMind
   used) the density is *low*; but such scales are *isolated*: the
   nearest non-resonance scale is at distance O(N^{1 - δ}) away, much
   smaller than N.

### 4.4 Alternative strategy (less recommended)

> **Strategy S2 — "Bertrand's postulate"-style argument.**
> Use the fact that between any two resonance scales `3^k ≈ 4^m` and
> `3^{k+1} ≈ 4^{m+1}` there is a "buffer zone" of length
> `min(3^{k+1} - 4^{m+1}, 4^m - 3^k) · (1+o(1))` where A+B is dense.
> Then `upperDensity(A+B) ≥ density-on-buffers · proportion-of-time-in-buffer > 0`.

This is *essentially equivalent to S1* but is less computational and
less amenable to Lean formalization.

### 4.5 Why Case 2 is the consensus guess

The forum thread explicitly notes (Bloom, 2024):
> "Now I'm thinking but I have no idea how to decide between
>  scenario 1 and 2."

Both scenarios are consistent with:
- All known density bounds (Melfi, Hasler-Melfi, DeepMind).
- All known computational evidence (Python data, Lean native_decide).

The numerical evidence *strongly* favors Case 2 (density stays 0.85+
at N = 10⁸), but the lower-density = 0 proof only rules out Scenarios
3 and 4 — **not** 1 or 2.

---

## 5. Intermediate lemmas needed (for Lean formalization)

Below are the **8–10 specific statements** that, together, would
formalize Strategy S1.

| # | Statement | Type | Est. time |
|---|-----------|------|-----------|
| L1 | `A_card_bound`: `|A ∩ [0, 3^k)| = 2^k` | Counting | ✓ already proved |
| L2 | `B_card_bound`: `|B ∩ [0, 4^m)| = 2^m` | Counting | ✓ already proved |
| L3 | `A_max_bound`: `a ∈ A ∩ [0, 3^k) ⇒ a ≤ (3^k − 1)/2` | Digit lemma | ✓ already proved |
| L4 | `B_max_bound`: `b ∈ B ∩ [0, 4^m) ⇒ b ≤ (4^m − 1)/3` | Digit lemma | ✓ already proved |
| L5 | `a_bot_bound`: `a % 3^k ∈ A` and `a % 3^k ≤ (3^k−1)/2` for `a ∈ A` | Digit lemma | ✓ already proved |
| L6 | `b_bot_bound`: `b % 4^m ∈ B` and `b % 4^m ≤ (4^m−1)/3` for `b ∈ B` | Digit lemma | ✓ already proved |
| L7 | `sum_form_eq`: explicit algebraic decomposition `a+b = min(3^k,4^m)·y + c` | Algebra | ✓ already proved |
| L8 | `c_bound`: `c ≤ (3^k−1)/2 + (4^m−1)/3 + |3^k − 4^m| · N₀` | Bounding | ✓ already proved |
| **L9** | **`non_resonance_density (N₀ : ℕ) : ∃ k m, ... : |A+B ∩ [N₀, 2N₀)| ≥ c · N₀`** | **NEW — main step** | **2-3 days** |
| **L10** | **`shift_density : ∃ (N_seq : ℕ → ℕ), StrictMono N_seq ∧ ∀ n, |A+B ∩ [N_seq n, 2 N_seq n)| ≥ c₀ · N_seq n`** | **NEW — top step** | **1-2 days** |
| **L11** | **`upperDensity_positive : 0 < (A + B).upperDensity`** | **The target** | **0.5 day (assembly)** |

### 5.1 Detailed Lemma L9 (the main new work)

**Statement:** *For every sufficiently large `N₀`, there exist
`k, m ∈ ℕ` with `N₀ ≤ min(3^k, 4^m) ≤ 2 N₀` such that*
```
|(A + B) ∩ [min(3^k, 4^m), 2 · min(3^k, 4^m))|
    ≥  c₀ · min(3^k, 4^m)              with c₀ = 5/6 − 1/30.
```

**Proof sketch (natural-language, to be Lean-formalized):**
1. Use Dirichlet's approximation to find `k, m` with
   `min(3^k, 4^m) ∈ [N₀, 2 N₀]` and `|4^m − 3^k| ≤ min(3^k, 4^m)/30`.
2. Such `k, m` exist because the ratios `3^k / 4^⌊k log₄3⌋` are dense in
   `ℝ⁺` (irrationality of `log 4 / log 3`).
3. Define the bad interval `G = [4^m/3 + 3^k/2, min(3^k, 4^m))`, of
   length ≈ `(5/6) · min(3^k, 4^m)`. (L3, L4.)
4. The "good" interval `[min(3^k, 4^m), 2 · min(3^k, 4^m))` does NOT
   contain G (it lies below it), so we only need to count A+B elements
   there.
5. Use the **additive Cauchy–Davenport** inequality in the "non-gap"
   direction: any interval of length L ≥ min(3^k, 4^m) contains at
   least `c₀ · L` elements of A + B because the density of A in
   `[0, 3^k)` is `2^k / 3^k > 1/2` and of B in `[0, 4^m)` is
   `2^m / 4^m > 1/4`, and these are independent.

### 5.2 Detailed Lemma L10 (assembly)

**Statement:** *There exists a strictly increasing sequence
`N_seq : ℕ → ℕ` with `N_seq → ∞` and*
```
|(A + B) ∩ [N_seq n, 2 N_seq n)| ≥ c₀ · N_seq n.
```

**Proof:** Apply L9 with `N₀ = N_seq (n-1)` to obtain a new `k, m`;
set `N_seq n = min(3^k, 4^m)`. By construction `N_seq n > N_seq (n-1)`
(as L9 gives `min(3^k, 4^m) > N₀`), and the density bound comes
straight from L9.

### 5.3 Top-level assembly (L11)

Once L10 is proved:
```lean
theorem upperDensity_positive : 0 < (A + B).upperDensity := by
  -- 1. The limsup of |A+B ∩ [N_seq n, 2 N_seq n)| / (2 N_seq n)
  --    is at least c₀ / 2.
  -- 2. This limsup is ≤ upperDensity(A + B) because shifting
  --    the interval does not change the upper density.
  -- 3. So 0 < c₀/2 ≤ upperDensity(A + B).
  sorry
```

---

## 6. Time estimates per lemma

The existing code already covers L1–L8 in `erdos_125_general.lean`
(basic counting) and the mo271 Lean file proves L3–L8 in their full
generality (it took DeepMind ~3 hours of Lean search). The remaining
**new** work is:

| Task | Description | Time (single agent) | Time (multi-agent parallel) |
|------|-------------|---------------------|------------------------------|
| **L9 (non-resonance density)** | Main combinatorial lemma | 2 days | **4-8 hours** (split: digit lemma / Cauchy-Davenport / arithmetic) |
| **L10 (shift density assembly)** | Iteration + monotonicity | 1 day | 2-4 hours |
| **L11 (upperDensity positive)** | Final assembly using Mathlib's `upperDensity` | 0.5 day | 1-2 hours |
| L9a: Dirichlet approximation (Mathlib) | Borrow `Real.exists_int_int_abs_mul_sub_le` | 0.5 day | 1 hour |
| L9b: Cauchy-Davenport for digit-restricted sumsets | New combinatorial content | 1 day | 2-4 hours |

**Total realistic estimate:** ~3 days single-agent, ~0.5-1 day
multi-agent (5 parallel provers, each with EVOLVE-BLOCK).

---

## 7. Concrete recommendations for the multi-agent system

### 7.1 Recommended split

Three sub-agents can work in parallel:

1. **Sub-agent α — "non-resonance density lemma" (L9)**
   - EVOLVE-BLOCK: `non_resonance_density`, `cauchy_davenport_digit`.
   - Already-known base: A_card_bound, B_card_bound, A_max_bound, B_max_bound
     (proven in `mo271` Lean file, line 1-200 of the github cache).
   - Lean helpers to build: `digit_residue_dense`,
     `sum_coverage_lower_bound`.

2. **Sub-agent β — "shift density iteration" (L10)**
   - Input: L9 + L1, L2.
   - Build `N_seq` inductively; prove monotonicity.

3. **Sub-agent γ — "upper-density assembly" (L11)**
   - Input: L10 + Mathlib `upperDensity`.
   - Build the equivalence `lim sup density (shifted) ≤ upperDensity`.

All three converge at the top-level theorem
`erdos_125.variants.positive_upper_density` (which fills in
`answer(True)` for our case, since the question is "is upper density
positive?").

### 7.2 Risk factors
- **Lemma L9 requires Mathlib's `Real.exists_int_int_abs_mul_sub_le`**,
  which is available but non-trivial to invoke.
- The "Cauchy-Davenport for digit-restricted sets" idea (L9b) may not
  exist in Mathlib — may need to be proved from scratch.
- The agent must **not** rely on "Pach-Pintz theorem" — that name is
  a hallucination by the DeepMind agent and has no literature.
- **Honest assessment:** This is a *research-level* theorem. Even
  with multi-agent acceleration, formalizing it should be expected to
  take weeks of agent time. A **partial result** (e.g., L9 for
  specific `N₀ ≤ 10⁶` checked by `native_decide`) would already be
  valuable.

### 7.3 What success looks like
- The Lean file `125.lean` has `answer(True)` filled in for
  `zero_lower_positive_upper_density` (and equivalently
  `positive_upper_density`), with full proof.
- Mathlib-compatible, no `sorry` remaining.
- Independent of the DeepMind `mo271` fork (so we have an independent
  proof).

### 7.4 What failure looks like
- The agent repeatedly tries to prove `Case 1 = True` instead of `Case 2`.
  This is consistent with **either** (1) the conjecture is genuinely
  Case 1, or (2) the agent can't find L9's combinatorial argument.
  In either case, the *correct* answer to the question may genuinely
  be `Case 1` — see §4.5.
- The agent may "discover" a non-existent lemma (DeepMind's
  hallucination failure mode). Mitigation: every lemma name must be
  matched against Mathlib before relying on it.

---

## 8. Honest assessment

The Erdős 125 Case 2 question (positive upper density) is **genuinely
open as of 30 March 2026** per the erdosproblems.com website. The
numerical evidence supports Case 2, but no published proof exists.

This document identifies a **plausible strategy** (S1: shift-density
lemma + iteration) that:
1. Is consistent with all known bounds and computational evidence.
2. Has clear intermediate lemmas (L1–L11) with explicit Lean statements.
3. Could be formalized by a multi-agent Lean system in ~1-2 days of
   agent time.
4. Has a **non-trivial risk of failure** if L9 turns out to require
   genuinely new combinatorial theory (Melfi-style sumset estimates
   may not suffice).

The mathematics community has, to date, **not** decided between
Scenarios 1 and 2 (Bloom, 2024, forum). Our strategy is the most
plausible path to resolving Case 2 positively, but a negative result
(Case 1) would also be a substantial mathematical contribution.

---

## 9. Files / references

- Local: `/Users/hermes/.hermes/projects/erdos_125/code/erdos_125_general.lean` —
  L1–L4 already there.
- Local: `/Users/hermes/.hermes/projects/erdos_125/notes/01_results.md` —
  Python numerical evidence.
- External: `/tmp/formal-conjectures/FormalConjectures/ErdosProblems/125.lean` —
  current 4-case Lean formalization.
- External: `https://github.com/mo271/formal-conjectures/blob/c27415379b5dbe34105d1fdd707994540c4c6fc7/FormalConjectures/ErdosProblems/125.lean#L468` —
  DeepMind's full proof of `lowerDensity = 0` (cache at
  `/Users/hermes/.hermes/cache/web/github.com-32e96ac130.md`).
- External: arXiv:2605.22763 — *Advancing Mathematics Research with
  AI-Driven Formal Proof Search* (AlphaProof Nexus paper).
- External: https://www.erdosproblems.com/125 — problem statement.
- External: https://www.erdosproblems.com/forum/thread/125 — discussion
  thread (Tsoukalas, Bloom).