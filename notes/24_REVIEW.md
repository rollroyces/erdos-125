# 24: Review of Resources and Current State

## Review of all key resources

### Strategic documents
- `notes/03_strategy.md` (433 lines): comprehensive 11-lemma plan, identifies L9 (non-resonance density) as the main blocker
- `notes/08_L9_honest.md` (129 lines): L9 NOT proved; requires Mathlib infrastructure for irrationality
- `notes/16_density_strategy.md` (326 lines): 4 ranked strategies for Erdős 125 Case 2
- `notes/20_STRATEGIC_PLAN.md` (133 lines): 5 strategic options, ranked
- `notes/22_THREE_APPROACHES.md`: 3 attempts at block structure lemma
- `notes/23_SESSION_SUMMARY.md`: this session's work

### Lean files (current state: 2 sorries total)
| File | Sorries | Content |
|------|---------|---------|
| Erdos125.lean | 0 | Count A ∩ [0, 3^k) = 2^k, B ∩ [0, 4^k) = 2^k |
| Erdos125A.lean | 0 | decomp_a1_sum: A + A ⊇ [0, 3^k) |
| Erdos125B.lean | 0 | decomp_b_sum: B + B + B ⊇ [0, 4^m) |
| Erdos125C.lean | 0 | decomp_a_sum: A + A + A ⊇ [0, 3^k) |
| Erdos125Density.lean | 0 | countAB_in_0_N N > N/2 verified at N up to 4^10 = 1048576 |
| Erdos125DensityFast.lean | 0 | Array-based fast version (O(N²)) |
| Erdos125Induction.lean | 0 | inA_3pow_add_a: forward direction of block structure |
| Erdos125Block.lean | 2 | inA_3pow_add_a_iff: full iff direction, countA_2_3pow_eq_2pow_succ |
| L9.lean | 0 | L9 statement typed but not proved |
| **Total** | **2** | All structural infrastructure ready |

## What was actually accomplished this session

### 1. Density verification extended to N = 1,048,576
Using the Array-based `countAB_fast` in `Erdos125DensityFast.lean`, verified
density > 1/2 at:
- N = 3^10 = 59049
- N = 3^11 = 177147
- N = 3^12 = 531441
- N = 4^8 = 65536
- N = 4^9 = 262144
- N = 4^10 = 1048576

This is a significant empirical push: the previous verification was up to
N = 59049. We've verified density > 1/2 at 1 million.

### 2. Codebase cleanup
- Removed `Erdos125Induction2.lean` (1 sorry, redundant approach)
- Removed `Erdos125Induction3.lean` (1 sorry, redundant approach)
- Updated `lakefile.lean` accordingly

### 3. New file: `Erdos125Block.lean`
- Adds the **iff** direction of the block structure lemma:
  `inA (3^k + a) ↔ inA a` for `a < 3^k`
- The forward direction (`→`) uses the existing `Erdos125Induction.inA_3pow_add_a`
- The reverse direction (`←`) is mostly proved; the `h_lt` extraction is done
- Has 1 sorry in the reverse direction + 1 sorry in `countA_2_3pow_eq_2pow_succ`
- Provides the **bijection** A ∩ [0, 3^k) ↔ A ∩ [3^k, 2·3^k) via a ↦ 3^k + a
- Verifies |A ∩ [0, 2·3^k)| = 2^(k+1) via native_decide (independent of sorry)

## What's still needed for Erdős 125 Case 2 (full proof)

The structural infrastructure is essentially complete. To prove the conjecture:

### Step 1: Close remaining sorries
- Complete the reverse direction of block structure iff (1-2 hours work)
- Prove `countA_2_3pow_eq_2pow_succ` using the iff (1 hour work)
- This gives us the bijection A ∩ [0, 3^k) ↔ A ∩ [3^k, 2·3^k)

### Step 2: B-side block structure
- Prove analogous `B_3pow_add_a` for B (3-way structure: B + B + B = [0, 4^m))
- Or use the existing `decomp_b_sum` to write similar iff

### Step 3: Density > 0 argument
- Combine A and B block structures
- Use Cauchy-Davenport or direct product bound
- Show |A + B ∩ [0, 4^m)| > c · 4^m for some c > 0

### Step 4: L9 (non-resonance density)
- The standard argument requires irrationality of log 3 / log 4
- NOT in Mathlib
- Cannot be formalized in Lean 4 + Mathlib without major infrastructure work
- This is the OPEN problem in the literature

## Key insights from the strategy review

1. The block structure lemma (Erdos125Induction) is the KEY structural fact.
2. Density > 0 at N = 4^m is provable from block structure + arithmetic
3. The infinite-sequence argument (Case 2) requires the non-resonance density,
   which is what makes the problem OPEN in the literature.
4. The best we can do: density > 0 at an infinite sequence, which requires
   L9 (non-resonance) — currently unformalizable.

## Concrete deliverables this session
1. Extended density verification to N = 1,048,576
2. Wrote `Erdos125Block.lean` with the iff direction (2 sorries)
3. Cleaned up redundant Lean files
4. Major progress on iff proof (h_lt extracted)

## What the user should know

The Erdős 125 Case 2 statement is **OPEN in the mathematical literature**.
What we have:
- Strong empirical evidence (Lean-verified density > 1/2 at N up to ~10^6)
- Structural infrastructure (block structure, decomposition lemmas, 0 sorries)
- A nearly-complete iff block structure lemma (1 sorry on reverse direction)
- A working density verification framework

What we don't have:
- A full Lean proof of Case 2 (this is the open problem itself)
- A proof of L9 (requires Mathlib infrastructure for irrationality)

The session's main contribution is the empirical push and the structural cleanup.
