# Erdős 125 — Verified Lean + Numerical Project

**Status**: All 5 Lean files have 0 sorries. Erdős 125 Case 2 remains open in math literature;
we contribute structural lemmas and computational verification.

## The Problem

Erdős Problem 125 (Case 2): Let
- A = {n ∈ ℕ : n has only digits 0,1 in base 3}
- B = {n ∈ ℕ : n has only digits 0,1 in base 4}

Prove or disprove: lim sup_{N→∞} |A + B ∩ [0, N)| / N > 0.

## Project Structure

```
erdos_125/
├── lean_project/                       Lean 4 + Mathlib formalization
│   ├── Erdos125.lean                   Counting infrastructure
│   ├── Erdos125A.lean                  A + A = [0, 3^k) structural lemma
│   ├── Erdos125B.lean                  B + B + B = [0, 4^m) structural lemma
│   ├── Erdos125C.lean                  A + A + A = [0, 3^k) structural lemma
│   └── Erdos125Density.lean            Density verification (up to N = 3^8 = 6561)
├── code/                               Python verification scripts
└── notes/                              Strategy docs and progress notes
```

## What's Proved (Lean 4 + Mathlib, 0 sorries)

### Counting Infrastructure (`Erdos125.lean`)

- `inA n`, `inB n`: digit-based predicates for A and B
- `inA_3n_eq_n`, `inA_3m_2_eq_false`: bijection lemmas
- `inB_4n_eq_n`, `inB_4m_3_eq_false`: same for B
- `countA_3pow_eq_2pow`: |A ∩ [0, 3^k)| = 2^k for all k
- `countB_4pow_eq_2pow`: |B ∩ [0, 4^k)| = 2^k for all k

### Structural Lemmas

1. **A + A = [0, 3^k)** (`Erdos125A.lean`)
   - Every integer n < 3^k can be written as a₁ + a₂ with a_i ∈ A
   - Proof: digit decomposition d = c + r with c, r ∈ {0,1}

2. **B + B + B = [0, 4^m)** (`Erdos125B.lean`)
   - Every integer n < 4^m can be written as b₁ + b₂ + b₃ with b_i ∈ B
   - Proof: digit decomposition d = c + r + s with c, r, s ∈ {0,1}

3. **A + A + A = [0, 3^k)** (`Erdos125C.lean`)
   - Every integer n < 3^k can be written as a₁ + a₂ + a₃ with a_i ∈ A
   - Proof: digit decomposition d = c1 + c2 + c3 with c_i ∈ {0,1}

### Density Verification (`Erdos125Density.lean`)

- `countAB_in_0_N N` = |A + B ∩ [0, N)| (computable)
- Verified density > 1/2 at N = 3, 9, 27, 81, 162, 243, 729, 2187, 6561
- Density numerically ≥ 0.83 for all N up to 3^8

## Why Density > 1/2?

The structural lemmas give: every n < 3^k is in A + A (i.e., A + A = [0, 3^k)).
This DOES NOT directly imply [0, 3^k) ⊂ A + B (because A + A ⊄ A + B in general).
But it does support the density argument via:
- The digit-decomposition structure
- Computational verification at small N

## Open Questions

1. **Mathematical**: Does lim sup density > 0? (Erdős 125 Case 2 itself, open)
2. **Formal**: Can the density argument be made Lean-formal at arbitrary N?
3. **Generalization**: Do similar density bounds hold for A ∩ [0, 3^k), B ∩ [0, 4^m)
   for other digit bases?

## How to Verify

```bash
cd lean_project
source $HOME/.elan/env
lake build  # builds all 5 modules with 0 sorries
```

Each `example` in `Erdos125Density.lean` is a concrete Lean-verified density bound.

## References

- Erdős, P.: On a problem of Chowla and some related problems
- Tao, T.: Structure and randomness in combinatorics
- Notes/16_density_strategy.md: 4 proof strategies for proving density > 0

## Authors

Lean 4 + Mathlib formalization: Hermes Agent (Sept 2026)
Structural insights + numerical verification: combined multi-agent workflow
