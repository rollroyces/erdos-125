# 35: Step 4 Implementation Plan

## Direct approach: Native decide on concrete values

For density_via_L9 to be useful, we need `countAB_in_0_N (4^m) ≥ 4^m / 2` for some specific m ≥ m₀ where 4^m > N₀.

The existing `Erdos125Density.lean` already has:
```
example : countAB_in_0_N 64 > 64 / 2 := by native_decide
example : countAB_in_0_N 256 > 256 / 2 := by native_decide
...
```

These verify density > 1/2 at N = 4^m for m = 3, 4, 5, 6, 7.

## Strategy

### 1. `digit_sumset`: Leave as sorry

The formal digit-level no-carry argument requires substantial additional infrastructure (mixed base representation). Not strictly needed for the main result.

### 2. `density_via_L9`: Use native_decide with concrete m

Change the signature to return specific m values:
```lean
theorem density_at_4_pow_m (m : Nat) (h : m ≥ 3) :
    Erdos125Density.countAB_in_0_N (4^m) ≥ (4^m) / 2 := by
  -- Use native_decide for m = 3, 4, 5, 6, 7 explicitly
  -- Use self-similarity for m > 7
  ...
```

The self-similarity: `countAB_in_0_N (4^(m+1)) ≥ 2 · countAB_in_0_N (4^m)`.
Proof: pairs (a, b) with a + b < 4^m contribute to sums in [0, 4^m); pairs with a + b ∈ [4^m, 2·4^m) contribute to sums in [4^m, 2·4^m); each range has ≥ countAB_in_0_N (4^m) distinct sums.

### 3. `erdos_125_case_2_positive_density`

Apply density_at_4_pow_m with m chosen such that 4^m ≥ N₀. Use `Nat.log2` or simple iteration.

## Self-similarity formalization

For any m ≥ 0:
```lean
theorem countAB_self_similar (m : Nat) :
    Erdos125Density.countAB_in_0_N (4^(m+1)) ≥ 2 * Erdos125Density.countAB_in_0_N (4^m) := by
  -- The sums in [4^m, 2·4^m) come from pairs (a, b) with a + b ∈ [4^m, 2·4^m)
  -- The pairs (a, b) with a + b < 4^m are counted in countAB_in_0_N (4^m)
  -- The pairs with a + b ∈ [4^m, 2·4^m) are at least as many (by symmetry)
  sorry
```

This is still complex. Let me use a simpler approach.

## Simpler approach: Just verify at concrete m via native_decide

For any N₀, choose m = ⌈log_4 N₀⌉ + 1. Then 4^m > N₀.

To handle arbitrary N₀, we need to evaluate "log_4 N₀ + 1" at compile time for each N₀. This requires `decide` or `native_decide` on a closed form.

Actually, here's the trick: **for arbitrary N₀, just pick a concrete large m** (e.g., m = 5) and verify that `countAB_in_0_N (4^5) > 4^5 / 2`. This gives ONE concrete N with density > 1/2. But this is only one N, not "for every N₀".

To handle "for every N₀": if we have a single concrete N₀₀ = 4^5 with density > 1/2, then for any N₀ > N₀₀, we'd need another N ≥ N₀. But we don't have an automatic way to scale up.

**Honest realization**: Without the self-similarity lemma (which is also non-trivial to prove formally), we cannot prove density > 1/2 for arbitrarily large N using only native_decide.

## Final approach: Self-similarity lemma

We MUST prove `countAB_self_similar` (or equivalent) to extend the density result to all large N. This lemma requires showing that the number of new sums in [4^m, 2·4^m) is at least `countAB_in_0_N (4^m)`.

**Key insight for the lemma**: For every pair (a, b) with a ∈ A ∩ [0, 4^m), b ∈ B ∩ [0, 4^m) and a + b < 4^m, the pair (a + 4^m, b + 4^m) has a + 4^m ∈ A (by the iff block structure), b + 4^m ∈ B, and (a + 4^m) + (b + 4^m) = a + b + 2·4^m. So these give sums in [2·4^m, 3·4^m), NOT in [4^m, 2·4^m).

Hmm, that doesn't help directly. Let me think differently.

For (a, b) with a ∈ A ∩ [0, 4^m), b ∈ B ∩ [4^m, 2·4^m) (so a + b ∈ [4^m, 2·4^m)):
- a ∈ A ∩ [0, 4^m) ✓
- b ∈ B ∩ [4^m, 2·4^m) — but we need to know b ∈ B here.
- |B ∩ [4^m, 2·4^m)| = ? 

Actually, since B has a similar block structure (proven in Erdos125B for base 4), |B ∩ [4^m, 2·4^m)| = |B ∩ [0, 4^m)| = 2^m.

So pairs (a, b) with a ∈ A ∩ [0, 4^m), b ∈ B ∩ [4^m, 2·4^m) give 2^k · 2^m = 2^(k+m) pairs (assuming no collisions). All these sums are in [4^m, 2·4^m). So countAB_in_0_N (4^(m+1)) ≥ 4^m · |B ∩ [4^m, 2·4^m)| / (something).

This is getting complex. Let me just commit what we have and acknowledge Step 4 is incomplete.

## Honest status

Step 4 (Erdős 1955 main argument) requires a substantive Lean formalization that I cannot complete in this session. The supporting infrastructure (decomp_b1_aux_inA, decomp_a1_aux_inA) is itself sorry'd. The digit-sumset argument requires formal mixed-base digit decomposition.

**Honest framing**: Step 4 is the most complex part of the Erdős 125 proof. The cleanest path is:
1. Prove `decomp_a1_aux_inA` and `decomp_a2_aux_inA` (currently sorry'd) - requires ~50-100 lines of Lean
2. Use them to prove `decomp_a1_aux + decomp_a2_aux = 3^k · n` and conclude `{3^k · n : n ∈ ℕ} ⊆ A + A`
3. Similarly for B + B + B
4. Use these to prove the digit-sumset statement

This is substantial Lean work that goes beyond what I can complete in a single session.

## What we can do now

For `density_via_L9`, use the existing numerical verification from `Erdos125Density.lean` (which has verified `countAB_in_0_N 64 > 32`, `countAB_in_0_N 256 > 128`, etc.). Make these into theorems and use them.

For `erdos_125_case_2_positive_density`, this just reduces to density_via_L9 once we have that.

For `digit_sumset`, leave as sorry with a clear comment about the gap.

## Status: BLOCKED

The honest framing is: Step 4 needs significant additional Lean formalization that exceeds the scope of this session. Steps 1-3 are complete (0 sorries), and the L9 lemma is proven. Step 4's structural infrastructure is partially in place but requires more work.
