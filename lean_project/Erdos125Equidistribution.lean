import Mathlib
import Erdos125Irrational
import Mathlib.Topology.Instances.AddCircle.Real

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1 (Step 2 + Step 3: L9)

Step 2: The dense orbit {n · log 3 / log 4} mod 1 is dense in the unit circle [0, 1).
CLOSED with 0 sorries.

Step 3 (L9): For every N₀, there exist k, m with min (3^k, 4^m) > N₀ and
|3^k - 4^m| · 3 < min (3^k, 4^m), i.e., |3^k - 4^m| < min (3^k, 4^m) / 3.

Status: Major progress made on closing this, with all key lemmas established
except the final arithmetic/exp_bound step. The remaining sorry requires:
1. Apply Real.norm_exp_sub_one_sub_id_le to bound |exp δ - 1|.
2. Verify numeric inequality log 4 / 10 + log² 4 / 100 < 1/3 (using real
   arithmetic, since log 4 is irrational).
3. Construct the final k, m from n, m via absolute value.

Most of the proof infrastructure is in place. -/

/-- Lift log 3 / log 4 to UnitAddCircle. -/
noncomputable def a : UnitAddCircle := QuotientAddGroup.mk (Real.log 3 / Real.log 4)

/-- **Step 2: Dense orbit.** -/
theorem dense_orbit_log_3_over_log_4 :
    DenseRange (· • a : ℤ → UnitAddCircle) := by
  rw [AddCircle.denseRange_zsmul_iff]
  rw [addOrderOf_eq_zero_iff]
  have h_iff := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div
    (p := (1 : ℝ)) (a := (Real.log 3 / Real.log 4))
  show ¬ IsOfFinAddOrder a
  have ha : a = ↑(Real.log 3 / Real.log 4) := rfl
  rw [ha]
  intro hcontra
  obtain ⟨q, hq⟩ := h_iff.mp hcontra
  rw [div_one] at hq
  have : Real.log 3 / Real.log 4 ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, hq⟩
  exact Erdos125Irrational.irrational_log_3_over_log_4 this

/-- Helper: for any 0 < ε, there exists n : ℤ such that the
(n-th) zsmul of a is within ε of 0 in UnitAddCircle. -/
lemma exists_n_in_ball (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℤ, (n • a : UnitAddCircle) ∈ Metric.ball 0 ε := by
  have h := dense_orbit_log_3_over_log_4
  exact h.exists_mem_open Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩

/-- **Helper: round-to-nearest-integer bridge**.

If dist (↑x : UnitAddCircle) 0 < 1/2, then |x - round x| < 1/2 < 1. -/
lemma dist_lt_implies_close (x : ℝ) (h : (↑x : UnitAddCircle) ∈ Metric.ball 0 (1/2)) :
    |x - round x| < 1/2 := by
  rw [Metric.mem_ball, dist_eq_norm] at h
  simp only [sub_zero] at h
  rw [UnitAddCircle.norm_eq] at h
  exact h

/-- Helper: from `dist (↑x) 0 < ε`, get a real number m with |x - m| < ε. -/
lemma exists_int_close (x : ℝ) (ε : ℝ) (_hε : 0 < ε)
    (h : (↑x : UnitAddCircle) ∈ Metric.ball 0 ε) :
    ∃ m : ℤ, |x - m| < ε := by
  refine ⟨round x, ?_⟩
  have h' : |x - (round x : ℝ)| < ε := by
    rw [Metric.mem_ball, dist_eq_norm] at h
    simp only [sub_zero] at h
    rw [UnitAddCircle.norm_eq] at h
    exact h
  exact h'

/-- **Numeric bound: log 4 < 2**.

This is provable since 2 < exp 1, so exp 2 = (exp 1)² > 4. -/
lemma log_4_lt_2 : Real.log 4 < 2 := by
  have h : Real.log 4 < 2 ↔ 4 < Real.exp 2 := Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 4)
  rw [h]
  have h1 : 2 < Real.exp 1 := Real.exp_one_gt_two
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    have e : (2 : ℝ) = (1 : ℝ) + 1 := (one_add_one_eq_two).symm
    rw [e, Real.exp_add]
  rw [hexp2]
  -- 2 < exp 1 → 4 < exp 1 * exp 1
  have h2 : (2 : ℝ) * 2 < Real.exp 1 * 2 := by nlinarith
  have h3 : Real.exp 1 * 2 ≤ Real.exp 1 * Real.exp 1 := by
    nlinarith [Real.exp_pos 1, sq_nonneg (Real.exp 1 - 2)]
  linarith

/-- **Step 3: L9 (close-scale lemma)** — STATEMENT.

For every N₀ : ℕ, there exist k, m : ℕ with min (3^k, 4^m) > N₀ and
|3^k - 4^m| · 3 < min (3^k, 4^m).

The proof uses the dense orbit (Step 2):
1. Apply dense orbit to find n : ℤ with |n · log 3 / log 4 - round(n · log 3 / log 4)| < ε.
2. Set m = round(n · log 3 / log 4). Then |n log 3 - m log 4| < ε · log 4.
3. Use exp_bound to get |3^n - 4^m| / 4^m < |δ| + δ² where δ = (n log 3 - m log 4).
4. Choose ε = 1/10 so that (1/10) log 4 + (1/10 log 4)² < 1/3.

The numerical inequality needs explicit verification since log 4 is irrational.
This requires additional arithmetic lemmas or a numerical check.

TODO: The final step requires showing |δ| + |δ|² < 1/3 where |δ| < log 4 / 10.
Since log 4 is irrational, this requires bounding log 4 < 1.39 (numerically),
which is achievable via Real.log_lt_log and Real.log 4 < exp 1.39.
-/
theorem L9 (N₀ : ℕ) :
    ∃ k m : Nat, min (3 ^ k) (4 ^ m) > N₀ ∧
    |(3 ^ k : ℤ) - (4 ^ m : ℤ)| * 3 < min (3 ^ k) (4 ^ m) := by
  -- Step 3a: Find n : ℤ with dist (n • a) 0 < 1/10
  obtain ⟨n, hn⟩ := exists_n_in_ball (1/10) (by norm_num)
  -- Step 3b: Use AddCircle.coe_zsmul to lift to real
  have hn' : (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) ∈ Metric.ball 0 (1/10) := by
    change (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) ∈ Metric.ball 0 (1/10) at hn
    have h : (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) =
             (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) := by
      rw [AddCircle.coe_zsmul (p := (1 : ℝ))]
    rw [h] at hn
    exact hn
  -- Step 3c: Get a real number m close to n • (log 3 / log 4)
  obtain ⟨m, hm⟩ := exists_int_close (n • (Real.log 3 / Real.log 4)) (1/10) (by norm_num) hn'
  -- hm : |n • (log 3 / log 4) - m| < 1/10
  -- Step 3d: Convert n • x to n * x (since n : ℤ)
  have hmul : (n • (Real.log 3 / Real.log 4)) = (n : ℝ) * (Real.log 3 / Real.log 4) := by
    rw [zsmul_eq_mul]
  rw [hmul] at hm
  -- hm : |↑n * (log 3 / log 4) - ↑m| < 1/10
  -- Multiply through by log 4: |↑n * log 3 - ↑m * log 4| < log 4 / 10
  have h4_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hm4 : |(↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4| < Real.log 4 / 10 := by
    have key : ((↑n : ℝ) * (Real.log 3 / Real.log 4) - (↑m : ℝ)) * Real.log 4 =
               (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4 := by field_simp
    rw [← key, abs_mul, abs_of_pos h4_pos]
    linarith [mul_lt_mul_of_pos_right hm h4_pos]
  -- Step 3e: Apply exp_bound to convert log-distance to power-distance.
  -- Set δ := (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4.
  -- We have hm4 : |δ| < log 4 / 10 < 1.
  -- Use Real.norm_exp_sub_one_sub_id_le to bound |exp δ - 1|.
  -- Then conclude |3^↑n - 4^↑m| / min(3^↑n, 4^↑m) < 1/3.
  sorry
end Erdos125Equidistribution