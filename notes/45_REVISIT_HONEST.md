# 45: Revisiting Both Sorries — Honest Limits

## Line 71: `digit_sumset`

**Tried**: For `n < 3^k`, find `a ∈ A, b ∈ B` with `a < 3^k, b < 4^m, a + b = n`.

**Honest assessment**: This requires the **Erdős 1955 mixed-radix decomposition**:
- For each digit `n_i` of `n` in base 12 (= lcm(3,4)), write `n_i = c_i + r_i` with `c_i ∈ {0,1,2}` (carries to A digit in base 3) and `r_i ∈ {0,1,2,3}` (B digit in base 4), with NO carries between digits.
- Then `a = Σ c_i 3^i ∈ A ∩ [0, 3^k)`, `b = Σ r_i 4^i ∈ B ∩ [0, 4^m)`, and `a + b = n`.
- This requires formalizing mixed-base representation in Lean, which is substantial.

**Conclusion**: Off the critical path. Leaving as sorry.

## Line 100: `density_via_L9` N₀ ≥ 65536

**Tried this turn**: New `countAB_in_0_N_v2` using `any`-based membership check (short-circuits).
**Result**: `lake build Erdos125CountAB` killed at 18+ min. **Slower** than the original concat-based version.

**Why it's hard**:
- The `any` short-circuit helps at runtime but `native_decide` still must traverse the entire search space to verify the result.
- `native_decide` on `countAB_in_0_N (4^9 = 262144)` requires evaluating ~4^18 = 6.87 × 10^10 operations. Even at 10^9 ops/sec, this is 60+ seconds in C; in Lean's interpreter it's much slower.

**Conclusion**: The only ways to close this sorry are:
1. **Structural doubling** (`countAB(4N) ≥ 2 countAB(N)`) — multi-hour Lean work.
2. **Mixed-base digit-sumset** — multi-hour Lean work.
3. **Accept the sorry** as a known limitation.

The current state PROVES Erdős 125 Case 2 for N₀ < 65536, which is a non-trivial result.

## Current state

- **2 active sorries**: `digit_sumset` (line 71, off critical path), `density_via_L9` (line 100, N₀ ≥ 65536).
- `Erdos125A.lean`: 0 active sorries ✅
- `Erdos125CountAB.lean`: 0 active sorries ✅
- Full project builds (8866 jobs) ✅
- Latest commit: `d731fc7` on `origin/main`
