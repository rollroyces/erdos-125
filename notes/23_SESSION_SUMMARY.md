# 23: Session Summary - Pushing the Block Structure Iff and Density Verification

## Achievements this session

### 1. Density verification extended
- **Up to N = 1,048,576** (4^10) with density > 1/2 verified
- 3^10, 3^11, 3^12 (= 59049, 177147, 531441) verified
- 4^8, 4^9, 4^10 (= 65536, 262144, 1048576) verified
- All via `Array.replicate`-based O(N²) computation in `Erdos125DensityFast.lean`

### 2. Cleaned up codebase
- Removed `Erdos125Induction2.lean` and `Erdos125Induction3.lean` (had sorries, redundant approaches)
- Updated `lakefile.lean` accordingly
- 7 files with 0 sorries (clean, working state)

### 3. New file: `Erdos125Block.lean`
- Adds iff direction of block structure: `inA (3^k + a) ↔ inA a` for `a < 3^k`
- Forward direction (`→`): uses existing `Erdos125Induction.inA_3pow_add_a`
- Reverse direction (`←`): has 1 sorry (tactic block in nested IH unfolding)
- Provides bijection A ∩ [0, 3^k) ↔ A ∩ [3^k, 2·3^k)
- Verifies |A ∩ [0, 2·3^k)| = 2^(k+1) via native_decide

### 4. Block structure proof status
- `Erdos125Induction.lean`: forward direction `inA a → inA (3^k + a)` proved (0 sorries)
- `Erdos125Block.lean`: iff direction partially proved (1 sorry on reverse)

## Honest assessment of remaining gap

The iff direction IS mathematically true (digit-removal argument), but the Lean proof
has been blocked by tactic issues around:
- `(n' + 1)` form unification in nested `cases a with | succ a' => ...` blocks
- `Nat.lt_div_iff_mul_lt` argument order issues
- The `.add` notation in `inA` def creating implicit parens

All three are mechanical issues; closing the sorry would take 1-2 more hours of
careful Lean work but is well within reach.

## What remains to actually prove Erdős 125 Case 2

Even with both directions of the block structure lemma, we still need:

1. **B-side block structure**: an analogous lemma for B.
   - B has 3-way block structure: B + B + B = [0, 4^m) (proved in Erdos125B)
   - But we need: for b ∈ B and b < 4^m, 4^m + b ∈ B (this is FALSE for general b)
   - The right analog: decomp_b_sum gives a decomposition of 4^m * n into 3 B-elements

2. **Cross-A+B density argument**: combine A's block structure with B's decomposition
   to show |A + B ∩ [0, 4^m)| > c · 4^m for some c > 0.

3. **L9 (non-resonance density)**: the standard argument needs irrationality of
   log_3/log_4, which is NOT in Mathlib.

## Total project state (Sept 7, 2026)

| File | Sorries | Notes |
|------|---------|-------|
| Erdos125.lean | 0 | Counting infrastructure |
| Erdos125A.lean | 0 | A+A=[0, 3^k) |
| Erdos125B.lean | 0 | B+B+B=[0, 4^m) |
| Erdos125C.lean | 0 | A+A+A=[0, 3^k) |
| Erdos125Density.lean | 0 | Density > 1/2 at many N up to 4^10 |
| Erdos125DensityFast.lean | 0 | Array-based version |
| Erdos125Induction.lean | 0 | Block structure (forward) |
| Erdos125Block.lean | 1 | Block structure (iff, sorry on reverse) |
| L9.lean | 0 | L9 statement (not proved, just typed) |
| **Total** | **1** | All structural work |

## Next concrete steps

1. Close the `Erdos125Block.inA_3pow_add_a_iff` reverse direction (1-2 hours work).
2. Use the iff to prove `|A ∩ [0, 4^m)|` cleanly (countAB_in_0_N with closed-form).
3. Use the B-side decomp_b_sum to write a similar `B_3pow_add_a_iff` for the 3-way case.
4. Combine to get the density > 0 result.
5. Address the L9 (non-resonance) gap (likely impossible in Lean 4 without serious infrastructure).
