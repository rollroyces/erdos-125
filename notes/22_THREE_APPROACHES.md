# 22: Three Approaches to the Block Structure Lemma

## Session result: Two new files, two different approaches

### Approach 1: `Erdos125Induction2.lean` (already existed)
Uses custom recursive `inA` definition. Block structure lemma has sorry
in the `.add` notation handling (Lean's implicit right-association in
`(3^k' * 3).add a' + 1` doesn't unify with the unfolded `inA` def).

### Approach 2: `Erdos125Induction3.lean` (NEW)
Uses Mathlib's `Nat.digits` and `Nat.ofDigits_inj_of_len_eq`. The
structural lemma is conceptually clean: digits of `3^k + a` for `a < 3^k`
are `digits 3 a ++ replicate (k - length (digits 3 a)) 0 ++ [1]`.

**Status**: 1 sorry in the main `inA_3pow_add_a` theorem. The full
proof requires:
1. `Nat.ofDigits` of the candidate list = `3^k + a` (proved in `hofd_L`)
2. Length of the candidate list = `k + 1` (proved in `hlen_L`)
3. All digits in the candidate list < 3 (proved in `h_lt_L`)
4. Length of `digits 3 (3^k + a)` = `k + 1` (proved in `len_eq`)
5. All digits of `3^k + a` are < 3 (proved in `h_lt_digits`)
6. Apply `Nat.ofDigits_inj_of_len_eq` to get digit-list equality
7. Conclude via `List.all_append`

Step 6 is the main blocker. `Nat.ofDigits_inj_of_len_eq` requires
multiple `by ...` proof terms as arguments, and Lean parser/tactic
issues prevent clean application.

### Approach 3: `Erdos125.lean` (already existed)
Uses recursive inA, the original in Erdos125.lean. This file has 0
sorries because it doesn't prove the block structure lemma.

## Mathlib tools used in Approach 2

- `Nat.digits` (little-endian digit list)
- `Nat.ofDigits`, `Nat.ofDigits_digits`, `Nat.ofDigits_singleton`
- `Nat.ofDigits_append`, `Nat.ofDigits_append_replicate_zero`
- `Nat.digitsAppend` (padded digit list)
- `Nat.ofDigits_inj_of_len_eq` (key uniqueness theorem)
- `Nat.digits_lt_base` (digit bound)
- `Nat.digits_length_le_iff` (length bound)
- `List.getLast_append_singleton`, `List.getLast_cons`

## The density argument (unaffected by sorry)

Once `inA_3pow_add_a` is closed, the density argument in
`Erdos125Density.lean` can be extended to give a rigorous symbolic
proof of the Erdős 125 Case 2 result.

## Final file state

| File | Sorries | Approach |
|------|---------|----------|
| Erdos125.lean | 0 | Recursive inA, no block structure |
| Erdos125A.lean | 0 | A+A=[0, 3^k) |
| Erdos125B.lean | 0 | B+B+B=[0, 4^m) |
| Erdos125C.lean | 0 | Alt B+B+B |
| Erdos125Density.lean | 0 | Density > 1/2 verified |
| Erdos125DensityFast.lean | 0 | O(1)-set version (abandoned) |
| Erdos125Induction.lean | 0 | Recursive inA infrastructure |
| Erdos125Induction2.lean | 1 | Custom recursive + .add blocker |
| Erdos125Induction3.lean | 1 | Mathlib Nat.digits + tactic blocker |
| **Total** | **2** | Both on the same block structure lemma |
