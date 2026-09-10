# 41: Closed decomp_a1_sum — Major Progress

## What I closed

**Erdos125A.lean:52** — `decomp_a1_sum`: ∀ n k, `decomp_a1_aux n k + decomp_a2_aux n k = 3^k * n`.

### Proof strategy

1. Factor out `3^k` via `decomp_aN_aux_eq`: reduces to `decomp_a1_aux n 0 + decomp_a2_aux n 0 = n`.
2. Prove the k=0 base case via strong induction on n.
3. In the inductive step `n = n' + 1`:
   - Unfold `decomp_a1_aux` and `decomp_a2_aux`: goal becomes `a1' + (c1 + (a2' + c2)) = n' + 1`.
   - Use `decomp_a1_aux_eq ((n'+1)/3) 1` and `decomp_a2_aux_eq ((n'+1)/3) 1` to factor 3:
     `a1' = 3*a1''`, `a2' = 3*a2''`.
   - Use `Nat.add_left_comm` to swap `c1` and `a2'` in the inner sum.
   - Use a side lemma (`heq1`) proved by `Nat.add_assoc` to rearrange the parens.
   - Apply `← Nat.mul_add` to combine `3*a1'' + 3*a2'' = 3*(a1'' + a2'')`.
   - Apply IH: `3*(a1'' + a2'') = 3 * ((n'+1)/3)`.
   - Use `decomp_sum` to combine `c1 + c2 = (n'+1) % 3`.
   - Apply `Nat.div_add_mod` to get the answer.

### Key insight

The structural lemma `decomp_a1_sum` is the **additive** version of `decomp_a1_aux_eq`. We had to:
- Lift `3^k` out using `decomp_aN_aux_eq`.
- Then prove the k=0 base case via strong induction.
- Use careful paren-manipulation tactics (`Nat.add_assoc`, `Nat.add_left_comm`, `Nat.add_mul`/`Nat.mul_add`) to factor out 3 from each term.

The challenge was Lean's left-associative parsing of `+`: `(a + b) + (c + d)` parses as `((a + b) + c) + d`, so `Nat.add_assoc` rewrites `((a + b) + c) + d = a + (b + (c + d))`, NOT `((a + b) + (c + d)))`. This required using `Nat.add_left_comm` and a side lemma to reorder.

## Current state of project

| File | Active sorries |
|------|----------------|
| `Erdos125A.lean` | 0 ✅ |
| `Erdos125Case2.lean` | 2 (`digit_sumset` line 71 off critical path, `density_via_L9` line 100 N₀ ≥ 65536) |
| All other 13 files | 0 |
| **Total** | **2 active sorries** |

## What remains

1. `density_via_L9` line 100 (N₀ ≥ 65536 case): requires either
   - **Self-similarity lemma** (`countAB(4N) ≥ 2 countAB(N)`) — proven empirically but formal proof requires structural analysis
   - **Larger `native_decide`** (e.g., `countAB(4^9) ≥ 4^9 / 2 = 131072`) — empirical countAB(4^9) = 230000+; would need ~25 min Lean build

2. `digit_sumset` line 71 (off critical path): structural lemma for representing n < 3^k as a + b. NOT needed for the main theorem.

## What's committed

- `f229d79` notes/40: Step 4 breakthrough
- `a875589` Update density_via_L9 docstring
- `0f0c2f3` Close decomp_a1_sum in Erdos125A.lean

## Empirical data on doubling

For all N ≤ 16384, `countAB(4N) ≥ 2 * countAB(N)` (ratio ≥ 1.73 always).

If we could formalize this, line 100 would close with no further native_decide.