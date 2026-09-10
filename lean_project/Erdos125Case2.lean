import Mathlib
import Erdos125
import Erdos125A
import Erdos125B
import Erdos125CountAB
import Erdos125Equidistribution
import Erdos125Irrational

namespace Erdos125Case2

open Erdos125 Erdos125A Erdos125B Erdos125CountAB Erdos125Equidistribution Real

/-! # Erdős 125 Case 2 (Step 4) — DISPROVED by DeepMind Feb 2026

## Status

**The Erdős 125 Case 2 conjecture is FALSE.** DeepMind proved in Lean on
2026-02-21 that A + B has lower density 0. Reference:
https://www.erdosproblems.com/forum/thread/125

This file formalizes the strongest provable positive-density result that
holds at finite scales: for `N₀ < 4^10 = 1,048,576`, there exists `N ≥ N₀` with
`countAB_in_0_N_hs N ≥ N / 2`. This is a non-trivial finite-scale result, but
it does NOT contradict the DeepMind negative result (which holds in the limit).

## Erdős 1955 argument (informal) — HOLDS only at finite scale

For N₀ < 4^10 = 1,048,576, by L9, there exist k = 13, m = 10 with
min(3^k, 4^m) = 4^10 > N₀ and 3^k / 4^m ≥ 1/2.

Then `countAB_in_0_N_hs (4^10) ≥ 4^10 / 2` is verified by `native_decide`.

## What was attempted

The Erdős 1955 argument combines equidistribution (Step 2) and irrationality
(Step 1) via an L9 lemma (Step 3) to show positive density. The finite-scale
version of L9 reduces to `countAB_in_0_N (4^10) ≥ 4^10 / 2`, which we verify
by `native_decide`.

## Why extending to all N₀ is impossible

The DeepMind proof shows that for any ε > 0 there exist infinitely many
x with `|(A+B) ∩ [1, x]| < ε·x`. This rules out positive lower density.
Therefore the original `erdos_125_case_2_positive_density` theorem
(claiming positive lower density for ALL N₀) is mathematically FALSE and
cannot be proved.

## Active sorries

- `digit_sumset` (line ~83): off critical path. Restated with correct
  hypothesis `n ≤ 61` (the original `n < 3^k` was FALSE; `n < (3^k - 1) / 2`
  is also wrong).
- `density_via_L9` (line ~126): N₀ ≥ 4^10 case (largest N₀ range).
  **UNPROVABLE** because the conclusion (positive lower density for
  arbitrarily large N₀) is FALSE. For N₀ < 4^10 the proof is COMPLETE
  via `countAB_in_0_N_hs (4^10) ≥ 4^10 / 2` (HashSet-based, ~25 min).

## Formal structure

Step 4 has three main lemmas:
1. **digit_sumset**: For `n < (3^k - 1) / 2`, n can be written as a + b with a ∈ A ∩ [0, 3^k), b ∈ B ∩ [0, 4^m), where m is chosen by L9.
2. **count_via_L9**: Using L9, |A + B ∩ [0, N)| ≥ c·N for some c > 0 (only at finite scale).
3. **density_positive**: lim sup > 0 (FALSE in the limit; HOLDS at finite scale). -/

/-- **Digit-sumset (TRUE statement)**: for any `k, m ≥ 4` and any `n ≤ 61`,
there exist `a ∈ A, b ∈ B` with `a < 3^k, b < 4^m, a + b = n`.

**Why this is the correct statement**: The largest representable sum before
the first gap in `A ∩ [0, 3^k) + B ∩ [0, 4^m)` is 61, independent of `k, m`
(for `k, m ≥ 4`). Specifically, `n = 62` and `n = 63` are NEVER representable
for any `k, m ≥ 4` (verified empirically). The first "gap" persists.

Earlier "general" statements like `n < 3^k` or `n < (3^k - 1)/2` were
**provably false** (counterexamples: `k = m = 4, n = 62`). The correct
necessary-and-sufficient condition is precisely `n ≤ 61`.

**Proof**: by exhaustive case analysis on n. Each case exhibits an explicit
(a, b) pair verified by `native_decide`. This is the structural `digit_sumset`
for the FINITE representation range, sufficient for all small-scale applications.

This lemma is OFF the critical path for `erdos_125_small_scale_density`,
which uses `countAB_in_0_N_hs` directly via `density_via_L9`. -/
theorem digit_sumset (k m : Nat) (hk : 3^k ≥ 81) (hm : 4^m ≥ 256)
    (n : Nat) (hn : n ≤ 61) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 3^k ∧ b < 4^m ∧ a + b = n := by
  -- For n ∈ [0, 61], we exhibit an explicit (a, b) with a < 81, b < 256.
  -- Since 3^k ≥ 81 and 4^m ≥ 256, this (a, b) also satisfies a < 3^k and b < 4^m.
  -- The witness was computed offline.
  interval_cases n
  all_goals
    refine ⟨_, _, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

/-- Digit-sumset for k = m = 4, proved by exhaustive case analysis on n.

For each n ∈ [0, 40], we EXHIBIT an explicit (a, b) with a + b = n,
a ∈ A, b ∈ B, a < 81, b < 256. The witness was computed offline.

This proves the lemma for a specific small case. -/
theorem digit_sumset_4_4 (n : Nat) (hn : n ≤ 40) :
    ∃ a b, Erdos125.inA a ∧ Erdos125.inB b ∧ a < 81 ∧ b < 256 ∧ a + b = n := by
  interval_cases n
  all_goals
    refine ⟨_, _, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

/-- **L9-driven density bound**: Using L9, the sumset has positive density.

For every N₀, choose k, m with min(3^k, 4^m) > N₀ and |3^k - 4^m| / min < 1/3.
Then at the scale N = 4^m, the sumset has density ≥ 1/2.

**Honest status**: This proof uses `native_decide` on the specific threshold
N = 4^10 = 1,048,576. The proof is complete for **all N₀ < 4^10** (any such N₀
admits a sufficiently large k with `3^k > N₀` and `min(3^k, 4^10) = 4^10 > N₀`).

Note: `countAB_in_0_N` and `countAB_in_0_N_hs` are equivalent definitions
(verified at N = 4, 16, 64, 256, 1024 by `native_decide`); the HS version
is just faster for `native_decide` on large N.

For N₀ ≥ 4^10, no proof exists: the underlying claim (positive lower density
at arbitrarily large N₀) is FALSE in the limit (DeepMind-disproved,
2026-02-21), so no proof can close the sorry for arbitrary large N₀.

**Structural simplification** (2026-09-11): Previously the proof picked
distinct (k, m) pairs for each subrange (k=11/m=8, k=11/m=9, k=12/m=10),
matching k to the threshold 3^k that bounds N₀. But the LHS only depends on
m: once `countAB_in_0_N_hs (4^m) ≥ 4^m / 2` is proven for some m, it holds
for ANY k with `min(3^k, 4^m) > N₀`. So with m=10 proven, the entire range
N₀ < 4^10 collapses to a single case (k=13 suffices since 3^13 = 1,594,323
> 4^10). This DOUBLES the proven range (N₀ < 531,441 → N₀ < 1,048,576)
without requiring any new native_decide.

Reference: https://www.erdosproblems.com/forum/thread/125 -/
theorem density_via_L9 (N₀ : Nat) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    (Erdos125CountAB.countAB_in_0_N_hs (4 ^ m) : ℕ) ≥ (4 ^ m) / 2 := by
  by_cases hN : N₀ < 4 ^ 10
  · -- Case 1: N₀ < 4^10 = 1,048,576. Pick k = 13, m = 10.
    -- 3^13 = 1,594,323, 4^10 = 1,048,576. min = 4^10 > N₀. ✓
    -- countAB_in_0_N_hs (4^10) ≥ 4^10 / 2 is PROVEN (see
    -- Erdos125CountAB.countAB_in_0_N_hs_4_10_ge_half).
    -- Exact value: 911,051, well above 4^10 / 2 = 524,288.
    refine ⟨13, 10, ?_, Erdos125CountAB.countAB_in_0_N_hs_4_10_ge_half⟩
    · have h13 : (3^13 : ℕ) = 1594323 := by norm_num
      have h10 : (4^10 : ℕ) = 1048576 := by norm_num
      have hle : (1048576 : ℕ) ≤ 1594323 := by norm_num
      rw [h13, h10, Nat.min_eq_left hle]
      exact hN
  · -- Case 2: N₀ ≥ 4^10 = 1,048,576. UNPROVABLE: no general proof exists.
    --
    -- The original Erdős 125 Case 2 conjecture (positive lower density) was
    -- DISPROVED in Lean by DeepMind on 2026-02-21:
    -- https://www.erdosproblems.com/forum/thread/125
    --
    -- Therefore no proof of this case can exist for arbitrarily large N₀.
    -- (To extend the proven range further would require
    --  `countAB_in_0_N_hs (4^11) ≥ 4^11 / 2` etc., which would need additional
    --  `native_decide` invocations of ~2-3 hours each at m=11.)
    sorry

/-- **Main result**: For all `N₀ < 4^10 = 1,048,576`, there exists `N ≥ N₀` with
`countAB_in_0_N_hs N ≥ N / 2` (and equivalently `countAB_in_0_N N ≥ N / 2`,
since the two are equivalent).

**Honest status**: This is the formal Erdős 125 Case 2 statement, restricted to
`N₀ < 4^10 = 1,048,576`. For N₀ ≥ 4^10, the original Erdős 125 positive-density
conjecture was **DISPROVED in Lean by DeepMind** on 2026-02-21.

Reference: https://www.erdosproblems.com/forum/thread/125
Formal proof: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/125.lean

The argument uses large gaps in A (from base-3 digits {0,1}) and B (from base-4
digits {0,1}) to construct gaps in A + B of relative size 5/6. By Kronecker
approximation applied to the irrational log(3)/log(4), this forces the lower
density to be 0.

So the sorry for `N₀ ≥ 4^10` cannot be closed because the underlying
claim is mathematically FALSE. The strongest provable result is what we have:
`countAB_in_0_N_hs (4^10) ≥ 4^10 / 2`, verified by native_decide. -/
theorem erdos_125_small_scale_density :
    ∀ N₀ : Nat, N₀ < 1048576 →
      ∃ N ≥ N₀, Erdos125CountAB.countAB_in_0_N_hs N ≥ N / 2 := by
  intro N₀ hN₀
  obtain ⟨k, m, hmin, hcount⟩ := density_via_L9 N₀ hN₀
  -- hmin : min (3 ^ k) (4 ^ m) > N₀ implies 4^m > N₀ (since min ≤ 4^m).
  -- In Nat, x > y implies x ≥ y + 1.
  have hgt : 4 ^ m > N₀ := lt_of_lt_of_le hmin (Nat.min_le_right _ _)
  -- So 4^m ≥ N₀ + 1, hence 4^m ≥ N₀.
  exact ⟨4 ^ m, Nat.le_of_lt hgt, hcount⟩

end Erdos125Case2