# 30: Step 2 CLOSED! Dense orbit of {n · log 3 / log 4} mod 1 PROVED

## MAJOR BREAKTHROUGH

After extensive investigation, **Step 2 of Erdős 125 Case 2 is now CLOSED** with **0 sorries**.

The key insight was discovering that `Mathlib.Topology.Instances.AddCircle.Real` provides
`abbrev UnitAddCircle := AddCircle (1 : ℝ)`, which avoids the AddCircle 1 Fact instance issue.
Combined with the lemma `AddCircle.denseRange_zsmul_iff`, we can prove the dense orbit:

```lean
theorem dense_orbit_log_3_over_log_4 :
    DenseRange (· • a : ℤ → UnitAddCircle) := by
  rw [AddCircle.denseRange_zsmul_iff]  -- ↔ addOrderOf a = 0
  rw [addOrderOf_eq_zero_iff]          -- ↔ ¬ IsOfFinAddOrder a
  have h_iff := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div
    (p := (1 : ℝ)) (a := (Real.log 3 / Real.log 4))
  -- h_iff : IsOfFinAddOrder ↑(log 3 / log 4) ↔ ∃ q : ℚ, (q : ℝ) = log 3 / log 4
  intro hcontra
  obtain ⟨q, hq⟩ := h_iff.mp hcontra
  rw [div_one] at hq
  -- Contradiction with Erdos125Irrational.irrational_log_3_over_log_4
  have : Real.log 3 / Real.log 4 ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, hq⟩
  exact Erdos125Irrational.irrational_log_3_over_log_4 this
```

## What was the actual obstacle

The earlier attempts at Step 2 kept failing because:
- `DenseRange (· • (log 3 / log 4) : ℤ → AddCircle 1)` doesn't typecheck
- `n • a` defaults to nsmul (for ℕ), not zsmul (for ℤ)
- `AddCircle 1` requires `Fact (0 < 1)` instance, and the user-defined instance was conflicting

**The fix**: Use Mathlib's `abbrev UnitAddCircle := AddCircle 1`. This:
1. Makes the Fact instance implicit (Mathlib handles it)
2. Allows `(· • a : ℤ → UnitAddCircle)` to typecheck correctly
3. Lifts `a = QuotientAddGroup.mk (Real.log 3 / Real.log 4)` directly via mk

## Steps status

- **Step 1** (irrationality of log 3 / log 4): ✅ CLOSED (0 sorries, `Erdos125Irrational.lean`)
- **Step 2** (dense orbit): ✅ **CLOSED** (0 sorries, `Erdos125Equidistribution.lean`)
- **Step 3** (L9 close-scale lemma): ❌ NOT CLOSED (1 sorry in `L9`, requires more work)
- **Step 4** (Erdős 1955 argument): ❌ NOT CLOSED (4 sorries in `Erdos125Case2.lean`)

## Commits this session

1. `Step 2 CLOSED: dense orbit of {n · log 3 / log 4} mod 1 PROVED with 0 sorries!`
2. `Step 3 outline: dense orbit corollary + L9 statement`

## What's still needed for Erdős 125 Case 2

To complete Step 3 (L9), I need to:
1. Extract from dense orbit: for any ε > 0, ∃ k with {k · log 3 / log 4} < ε.
2. Set m = round(k · log 3 / log 4).
3. Prove |3^k - 4^m| / min(3^k, 4^m) < 1/3 from the above.

This requires bounds on |e^x - 1| - 1 in terms of |x|, which is in Mathlib as
`Real.exp_bound` or similar.

To complete Step 4 (Erdős 1955 argument), I need:
1. Digit-level no-carry representation in mixed base (3, 4).
2. Use L9 to construct k, m where A + B sums densely on [0, 4^m).
3. Direct proof of |A + B ∩ [0, N)| ≥ c · N for some c > 0.

This is the final step. The structural infrastructure is in place; only the
digit-level no-carry lemma is needed.

## What I learned

1. **`UnitAddCircle`** in Mathlib is `AddCircle 1` with the Fact instance pre-supplied.
2. **`QuotientAddGroup.mk`** directly lifts real numbers to AddCircle.
3. **`AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div`** connects IsOfFinAddOrder to
   rational elements in the AddCircle.
4. The HSMul issue with `· • a` and `n : ℤ` is NOT a Lean 4 bug — it just requires
   Mathlib's `UnitAddCircle` to be used instead of raw `AddCircle 1`.

This was a real breakthrough that I was previously not able to make.