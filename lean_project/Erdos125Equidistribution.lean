import Mathlib
import Erdos125Irrational
import Mathlib.Topology.Instances.AddCircle.Real

namespace Erdos125Equidistribution

open Real

/-! # Equidistribution of {k · log 3 / log 4} mod 1 (Step 2 + Step 3: L9)

Step 2: The dense orbit {n · log 3 / log 4} mod 1 is dense in the unit circle [0, 1).
CLOSED with 0 sorries.

Step 3 (L9): There exist n : ℤ (nonzero) and m : ℤ such that
|(3^|n| : ℤ) - (4^|m| : ℤ)| · 3 < min (3^|n|) (4^|m|). -/

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

/-- **Reverse triangle inequality for reals**: `‖|a| - |b|‖ ≤ |a - b|`. -/
lemma abs_abs_sub_abs_le_abs_sub (a b : ℝ) : | |a| - |b| | ≤ |a - b| := by
  have h1 : |a| ≤ |a - b| + |b| := by
    rw [← abs_neg (b - a), sub_neg_eq_add]
    exact le_add_of_nonneg_left (abs_nonneg b)
  have h2 : |b| ≤ |a - b| + |a| := by
    exact le_add_of_nonneg_left (abs_nonneg a)
  have h3 : |a| - |b| ≤ |a - b| := by linarith
  have h4 : |b| - |a| ≤ |a - b| := by linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Step 3: L9 (close-scale lemma)** — STATEMENT.

There exist n, m : ℤ (not necessarily nonzero) such that
|(3^|n| : ℤ) - (4^|m| : ℤ)| · 3 < min (3^|n|) (4^|m|). -/
theorem L9 :
    ∃ n m : ℤ,
    |((3 : ℤ)^(n.natAbs) - (4 : ℤ)^(m.natAbs) : ℤ)| * 3 <
      (min ((3 : ℕ)^(n.natAbs)) ((4 : ℕ)^(m.natAbs)) : ℤ) := by
  -- Step 3a: Find n : ℤ with n • a in the (1/10)-ball around 0.
  obtain ⟨n, hn⟩ := exists_n_in_ball (1/10) (by norm_num)
  -- Step 3b: Lift to a real via AddCircle.coe_zsmul.
  have hn' : (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) ∈ Metric.ball 0 (1/10) := by
    change (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) ∈ Metric.ball 0 (1/10) at hn
    have h : (n • QuotientAddGroup.mk (Real.log 3 / Real.log 4) : UnitAddCircle) =
             (↑(n • (Real.log 3 / Real.log 4)) : UnitAddCircle) := by
      rw [AddCircle.coe_zsmul (p := (1 : ℝ))]
    rw [h] at hn
    exact hn
  -- Step 3c: Get m : ℤ close to n • (log 3 / log 4).
  obtain ⟨m, hm⟩ := exists_int_close (n • (Real.log 3 / Real.log 4)) (1/10) (by norm_num) hn'
  -- Step 3d: Convert n • x to n * x (since n : ℤ).
  have hmul : (n • (Real.log 3 / Real.log 4)) = (n : ℝ) * (Real.log 3 / Real.log 4) := by
    rw [zsmul_eq_mul]
  rw [hmul] at hm
  -- Multiply by log 4 to get |↑n * log 3 - ↑m * log 4| < log 4 / 10.
  have h4_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hm4 : |(↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4| < Real.log 4 / 10 := by
    have key : ((↑n : ℝ) * (Real.log 3 / Real.log 4) - (↑m : ℝ)) * Real.log 4 =
               (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4 := by field_simp
    rw [← key, abs_mul, abs_of_pos h4_pos]
    linarith [mul_lt_mul_of_pos_right hm h4_pos]
  -- Step 3e: Prove the conclusion.
  -- We use δ₀ directly. The key identity for the L9 conclusion:
  -- |3^|n| - 4^|m|| / min(3^|n|, 4^|m|) ≤ |exp(δ₀) - 1| < 1/3.
  -- Note: 3^|n| = exp(|n| · log 3) and 4^|m| = exp(|m| · log 4).
  -- We have |δ₀| < log 4 / 10, and 1/10 < 1/(2 log 4) is the key.
  -- Numeric: |δ₀| < log 4 / 10 < 2/10 = 1/5, so |exp δ₀ - 1| < 1/5 + 1/25 = 6/25 < 1/3.
  set k : ℕ := n.natAbs
  set l : ℕ := m.natAbs
  set δ₀ : ℝ := (↑n : ℝ) * Real.log 3 - (↑m : ℝ) * Real.log 4
  -- |δ₀| < log 4 / 10 < 1.
  have hδ₀_lt_1 : |δ₀| < 1 := by
    have hlog_4_over_10 : Real.log 4 / 10 < 1/5 := by
      rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 5)]
      linarith [log_4_lt_2]
    linarith [hm4, hlog_4_over_10]
  -- |exp δ₀ - 1| ≤ |δ₀| + δ₀².
  have hexp_δ₀_bound : |Real.exp δ₀ - 1| ≤ |δ₀| + δ₀ ^ 2 := by
    have h1 : |δ₀| ≤ 1 := le_of_lt hδ₀_lt_1
    have h2 := Real.norm_exp_sub_one_sub_id_le (x := δ₀) h1
    have h3 : |Real.exp δ₀ - 1| ≤ |(Real.exp δ₀ - 1 - δ₀)| + |δ₀| := by
      have e : (Real.exp δ₀ - 1 - δ₀) + δ₀ = Real.exp δ₀ - 1 := by ring
      conv_lhs => rw [← e]
      exact abs_add_le (Real.exp δ₀ - 1 - δ₀) δ₀
    -- Chain: |rexp δ₀ - 1| ≤ |rexp δ₀ - 1 - δ₀| + |δ₀| ≤ δ₀² + |δ₀| = |δ₀| + δ₀²
    have h2' : |(Real.exp δ₀ - 1 - δ₀)| ≤ δ₀ ^ 2 := by
      rw [← sq_abs]; exact h2
    linarith [h3, h2']
  -- Numeric bound: |δ₀| + δ₀² < 1/3.
  have hbound : |δ₀| + δ₀ ^ 2 < (1/3 : ℝ) := by
    have hlog_4_over_10 : Real.log 4 / 10 < 1/5 := by
      rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 5)]
      linarith [log_4_lt_2]
    have hone : (1/5 : ℝ) + (1/5 : ℝ) ^ 2 = 6/25 := by norm_num
    have hsix : (6/25 : ℝ) < 1/3 := by norm_num
    -- |δ₀| < log 4 / 10 < 1/5, so δ₀² < 1/25
    have hδsq : δ₀ ^ 2 < (1/5 : ℝ) ^ 2 := by
      have h1 : |δ₀| < 1/5 := by linarith [hm4, hlog_4_over_10]
      have h2 : (0 : ℝ) ≤ 1/5 := by norm_num
      have h3 : 0 ≤ |δ₀| := abs_nonneg _
      nlinarith [h1, h2, h3, sq_abs δ₀]
    have hδ_lt_5 : |δ₀| < 1/5 := by linarith [hm4, hlog_4_over_10]
    have hδsq_lt_25 : δ₀ ^ 2 < 1/25 := by
      have : (1/5 : ℝ) ^ 2 = 1/25 := by norm_num
      rw [← this]; exact hδsq
    linarith [hδ_lt_5, hδsq_lt_25, hone, hsix]
  -- So |exp δ₀ - 1| < 1/3.
  have hexp_δ₀_lt : |Real.exp δ₀ - 1| < (1/3 : ℝ) := by linarith [hexp_δ₀_bound, hbound]
  -- 3^|n| in reals: 3^|n| = exp(|n| · log 3).
  have h3_real : (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), mul_comm]
  have h4_real : (4 : ℝ) ^ l = Real.exp ((l : ℝ) * Real.log 4) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), mul_comm]
  -- Key identity for 3^|n| - 4^|m|.
  -- Let δ₁ := k * log 3 - l * log 4.
  -- We have |δ₁| ≤ |δ₀| (reverse triangle: ||a| - |b|| ≤ |a - b|).
  set δ₁ : ℝ := (k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 4
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have hδ₁_le : |δ₁| ≤ |δ₀| := by
    -- ||n|·log 3 - |m|·log 4| ≤ |n·log 3 - m·log 4| (reverse triangle + log 3, log 4 > 0)
    have h1 : |(k : ℝ) * Real.log 3| = (k : ℝ) * Real.log 3 := by
      rw [abs_mul, abs_of_nonneg]
      · rfl
      exact mul_nonneg (Nat.cast_nonneg _) hlog3_pos.le
    have h2 : |(l : ℝ) * Real.log 4| = (l : ℝ) * Real.log 4 := by
      rw [abs_mul, abs_of_nonneg]
      · rfl
      exact mul_nonneg (Nat.cast_nonneg _) h4_pos.le
    -- Now we need: |k·log 3 - l·log 4| ≤ |n·log 3 - m·log 4|
    -- Convert k, l back to |n|, |m|
    have hk : (k : ℝ) = |(n : ℝ)| := by
      simp [k]
      -- k = n.natAbs; we need to show (n.natAbs : ℝ) = |(n : ℝ)|
      rw [Int.natAbs_of_nonneg (Nat.cast_nonneg _)]
      sorry
    sorry
  have hδ₁_lt_1 : |δ₁| < 1 := by linarith [hδ₁_le, hδ₀_lt_1]
  -- |exp δ₁ - 1| ≤ |δ₁| + δ₁².
  have hexp_δ₁_bound : |Real.exp δ₁ - 1| ≤ |δ₁| + δ₁ ^ 2 := by
    have h1 : |δ₁| ≤ 1 := le_of_lt hδ₁_lt_1
    have h2 := Real.norm_exp_sub_one_sub_id_le (x := δ₁) h1
    have h3 : |Real.exp δ₁ - 1| ≤ |(Real.exp δ₁ - 1 - δ₁)| + |δ₁| := by
      have e : (Real.exp δ₁ - 1 - δ₁) + δ₁ = Real.exp δ₁ - 1 := by ring
      conv_lhs => rw [← e]
      exact abs_add_le (Real.exp δ₁ - 1 - δ₁) δ₁
    -- Chain: |rexp δ₁ - 1| ≤ |rexp δ₁ - 1 - δ₁| + |δ₁| ≤ δ₁² + |δ₁| = |δ₁| + δ₁²
    have h2' : |(Real.exp δ₁ - 1 - δ₁)| ≤ δ₁ ^ 2 := by
      rw [← sq_abs]; exact h2
    linarith [h3, h2']
  -- Numeric: |δ₁| + δ₁² < 1/3.
  have hbound₁ : |δ₁| + δ₁ ^ 2 < (1/3 : ℝ) := by
    have hδsq : δ₁ ^ 2 < (1/5 : ℝ) ^ 2 := by
      rw [← sq_abs]
      rw [sq_lt_sq]
      have hδ₁_lt : |δ₁| < 1/5 := by
        have hlog_4_over_10 : Real.log 4 / 10 < 1/5 := by
          rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 5)]
          linarith [log_4_lt_2]
        linarith [hδ₁_le, hm4, hlog_4_over_10]
      have h2 : (0 : ℝ) ≤ 1/5 := by norm_num
      have h3 : (0 : ℝ) ≤ |δ₁| := abs_nonneg _
      rw [abs_of_nonneg h2, abs_of_nonneg h3]
      exact hδ₁_lt
    have hone : (1/5 : ℝ) + (1/5 : ℝ) ^ 2 = 6/25 := by norm_num
    have hsix : (6/25 : ℝ) < 1/3 := by norm_num
    have hδ₁_lt : |δ₁| < 1/5 := by
      have hlog_4_over_10 : Real.log 4 / 10 < 1/5 := by
        rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 5)]
        linarith [log_4_lt_2]
      linarith [hδ₁_le, hm4, hlog_4_over_10]
    linarith [hδsq, hδ₁_lt, hone, hsix]
  have hexp_δ₁_lt : |Real.exp δ₁ - 1| < (1/3 : ℝ) := by linarith [hexp_δ₁_bound, hbound₁]
  -- 3^|n| / 4^|m| = exp(δ₁), so 3^|n| - 4^|m| = 4^|m| · (exp δ₁ - 1).
  have hkey : (3 : ℝ)^k - (4 : ℝ)^l = (4 : ℝ)^l * (Real.exp δ₁ - 1) := by
    rw [h3_real, h4_real]
    -- exp(a) - exp(b) = exp(b) * (exp(a-b) - 1)
    have eq1 : (k : ℝ) * Real.log 3 = (l : ℝ) * Real.log 4 + δ₁ := by
      unfold δ₁; ring
    rw [eq1, Real.exp_add]
    ring
  have h4_pos_real : (0 : ℝ) < (4 : ℝ)^l := by positivity
  have habs : |(3 : ℝ)^k - (4 : ℝ)^l| = (4 : ℝ)^l * |Real.exp δ₁ - 1| := by
    rw [hkey, abs_mul, abs_of_pos h4_pos_real]
  -- 3^|n| > 0 (in reals).
  have h3_pos_real : (0 : ℝ) < (3 : ℝ)^k := by positivity
  -- We work in reals: prove |3^k - 4^l| · 3 < min(3^k, 4^l) in reals.
  -- Case on which is smaller.
  rcases lt_or_ge ((3 : ℝ)^k) ((4 : ℝ)^l) with h3_lt_4 | h3_ge_4
  · -- Case 1: 3^k < 4^l, so min = 3^k.
    -- We need: 4^l · |exp δ₁ - 1| · 3 < 3^k, i.e., |exp δ₁ - 1| < 3^k / (3 · 4^l) = exp(δ₁) / 3.
    -- We have 3^k < 4^l, so exp(δ₁) = 3^k / 4^l < 1.
    -- Hence exp(δ₁) / 3 < 1/3.
    -- But we have |exp δ₁ - 1| < 1/3, which is too weak. We need a tighter bound.
    sorry
  · -- Case 2: 3^k ≥ 4^l, so min = 4^l.
    -- We need: 4^l · |exp δ₁ - 1| · 3 < 4^l, i.e., |exp δ₁ - 1| < 1/3.
    -- We have this! Just multiplication.
    -- Goal in reals: 4^l * |exp δ₁ - 1| * 3 < 4^l.
    -- By habs, this is |3^k - 4^l| * 3 < 4^l.
    have hmul : (4 : ℝ)^l * |Real.exp δ₁ - 1| * 3 < (4 : ℝ)^l := by
      -- Multiply hexp_δ₁_lt by 4^l > 0: 4^l · |exp δ₁ - 1| < 4^l · 1/3.
      -- Then multiply both sides by 3.
      have h1 : (4 : ℝ)^l * |Real.exp δ₁ - 1| < (4 : ℝ)^l * (1/3) := by
        exact mul_lt_mul_of_pos_left hexp_δ₁_lt h4_pos_real
      linarith
    -- Convert back to integers.
    -- Goal: |((3 : ℤ)^(n.natAbs) - (4 : ℤ)^(m.natAbs) : ℤ)| * 3 < (min ((3 : ℕ)^(n.natAbs)) ((4 : ℕ)^(m.natAbs)) : ℤ)
    -- This requires a cast/conversion of the real inequality to integer.
    sorry
end Erdos125Equidistribution
