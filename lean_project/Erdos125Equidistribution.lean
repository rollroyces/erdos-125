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
lemma abs_abs_sub_abs_le_abs_sub (a b : ℝ) : ‖|a| - |b|‖ ≤ |a - b| := by
  have h1 : |a| ≤ |a - b| + |b| := by
    rw [show |a| = |a - b + b| from by rw [show a = a - b + b from by ring]; congr; ring]
    exact abs_add_le (a - b) b
  have h2 : |b| ≤ |a - b| + |a| := by
    rw [show |b| = |b - a + a| from by rw [show b = b - a + a from by ring]; congr; ring]
    rw [abs_sub_comm]
    exact abs_add_le (b - a) a
  have h3 : |a| - |b| ≤ |a - b| := by linarith
  have h4 : |b| - |a| ≤ |a - b| := by linarith
  rw [show ‖|a| - |b|‖ = abs (|a| - |b|) from rfl, abs_le]
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
    -- We prove |δ₁| = ||n|·log 3 - |m|·log 4| ≤ |n·log 3 - m·log 4| = |δ₀|.
    -- Step 1: (k : ℝ) · log 3 = |(n : ℝ) · log 3| (since log 3 > 0)
    have hk_eq : (k : ℝ) * Real.log 3 = |(n : ℝ) * Real.log 3| := by
      -- Use simp to handle the cast of natAbs
      have hkcast : (k : ℝ) = |(n : ℝ)| := by
        show (n.natAbs : ℝ) = |(n : ℝ)|
        simp
      rw [abs_mul, abs_of_nonneg (hlog3_pos.le), hkcast]
    have hl_eq : (l : ℝ) * Real.log 4 = |(m : ℝ) * Real.log 4| := by
      have hlcast : (l : ℝ) = |(m : ℝ)| := by
        show (m.natAbs : ℝ) = |(m : ℝ)|
        simp
      rw [abs_mul, abs_of_nonneg (h4_pos.le), hlcast]
    -- Step 2: Apply reverse triangle inequality to a = ↑n·log 3, b = ↑m·log 4.
    -- hrev : |||n·log 3| - |m·log 4|| ≤ |↑n·log 3 - ↑m·log 4|
    have hrev := abs_abs_sub_abs_le_abs_sub ((n : ℝ) * Real.log 3) ((m : ℝ) * Real.log 4)
    -- Step 3: Show the goal's LHS equals hrev's LHS.
    -- Goal LHS = |δ₁| = |↑k·log 3 - ↑l·log 4|
    -- hrev LHS = ‖|↑n·log 3| - |↑m·log 4‖
    -- Use the congruences to flip hrev to the goal form.
    have hkey' : ‖|↑n * Real.log 3| - |↑m * Real.log 4|‖ = ‖↑k * Real.log 3 - ↑l * Real.log 4‖ := by
      show abs (|↑n * Real.log 3| - |↑m * Real.log 4|) = abs (↑k * Real.log 3 - ↑l * Real.log 4)
      rw [abs_sub_comm, ← hk_eq, ← hl_eq, abs_sub_comm]
    rw [hkey'] at hrev
    -- hrev now has form: goal_lhs ≤ |δ₀|
    exact hrev
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
    -- First, refine to provide the witness n, m.
    refine ⟨(n : ℤ), (m : ℤ), ?_⟩
    -- We need to prove: |3^(n.natAbs) - 4^(m.natAbs)| · 3 < min (3^(n.natAbs)) (4^(m.natAbs))
    -- We'll show exp δ₁ > 3/4, which gives |exp δ₁ - 1| = 1 - exp δ₁,
    -- and then 3 · (1 - exp δ₁) < exp δ₁, which gives the goal after multiplying by 4^l.
    have hδ₁_neg : δ₁ < 0 := by
      have hrat : Real.exp δ₁ = (3 : ℝ)^k / (4 : ℝ)^l := by
        rw [Real.exp_sub, ← h3_real, ← h4_real]
      have h_div_lt : (3 : ℝ)^k / (4 : ℝ)^l < 1 := by
        rw [div_lt_one h4_pos_real]
        exact h3_lt_4
      rw [← hrat] at h_div_lt
      have : Real.exp δ₁ < Real.exp 0 := by simpa [Real.exp_zero] using h_div_lt
      exact (Real.exp_strictMono).lt_iff_lt.mp this
    have h_abs_exp : |Real.exp δ₁ - 1| = 1 - Real.exp δ₁ := by
      have hre : Real.exp δ₁ < 1 := by
        have hrat : Real.exp δ₁ = (3 : ℝ)^k / (4 : ℝ)^l := by
          rw [Real.exp_sub, ← h3_real, ← h4_real]
        rw [hrat]
        rw [div_lt_one h4_pos_real]
        exact h3_lt_4
      rw [abs_of_neg (sub_neg_of_lt hre)]
      ring
    -- |δ₁| < log 4 / 10
    have hδ₁_lt_log4_10 : |δ₁| < Real.log 4 / 10 := by
      have hlog_4_over_10 : Real.log 4 / 10 < 1/5 := by
        rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 5)]
        linarith [log_4_lt_2]
      linarith [hδ₁_le, hm4, hlog_4_over_10]
    -- δ₁ > -log 4 / 10
    have hδ₁_gt_neg : δ₁ > -Real.log 4 / 10 := by
      have h₁ : -(Real.log 4 / 10) < δ₁ := (abs_lt.mp hδ₁_lt_log4_10).left
      rw [neg_div'] at h₁
      exact h₁
    -- Key claim: 3^10 ≤ 4^9 so -log 4 / 10 ≥ log (3/4).
    have hkey34 : -Real.log 4 / 10 ≥ Real.log (3 / 4 : ℝ) := by
      have hlt : (3 : ℝ)^10 ≤ 4^9 := by norm_num
      have h₂ : (10 : ℝ) * Real.log 3 ≤ 9 * Real.log 4 := by
        have h₁ : Real.log ((3 : ℝ)^10) ≤ Real.log (4^9 : ℝ) := by
          rw [Real.log_le_log_iff (by norm_num : (0:ℝ) < (3:ℝ)^10) (by norm_num : (0:ℝ) < 4^9)]
          exact hlt
        rwa [Real.log_pow, Real.log_pow] at h₁
      have h₄ : (9 * Real.log 4 - 10 * Real.log 3) / 10 ≥ 0 := by
        have h₅ : (9 : ℝ) * Real.log 4 ≥ (10 : ℝ) * Real.log 3 := h₂
        rw [ge_iff_le, ← sub_nonneg]
        linarith [h₅]
      have h₅ : -Real.log 4 / 10 + Real.log 4 - Real.log 3 ≥ 0 := by
        rw [show -Real.log 4 / 10 + Real.log 4 - Real.log 3 =
                  (9 * Real.log 4 - 10 * Real.log 3) / 10 by ring]
        exact h₄
      have h₆ : Real.log (3 / 4 : ℝ) = Real.log 3 - Real.log 4 := by
        rw [Real.log_div]
        · norm_num
        · norm_num
      rw [h₆]
      linarith [h₅]
    -- δ₁ > -log 4 / 10 ≥ log (3/4), so δ₁ > log (3/4)
    have hδ₁_gt_log34 : δ₁ > Real.log (3 / 4 : ℝ) := by
      exact lt_of_le_of_lt hkey34 hδ₁_gt_neg
    -- exp δ₁ > 3/4
    have hexp_δ₁_gt_3_4 : Real.exp δ₁ > (3 / 4 : ℝ) := by
      rw [← Real.exp_log (by norm_num : (0:ℝ) < 3/4)]
      exact (Real.exp_strictMono).lt_iff_lt.mpr hδ₁_gt_log34
    -- Real inequality: |3^k - 4^l| * 3 < 3^k (close the integer goal with this).
    have hmul : |(3 : ℝ)^k - (4 : ℝ)^l| * 3 < (3 : ℝ)^k := by
      rw [habs, h_abs_exp]
      -- Goal: 4^l * (1 - exp δ₁) * 3 < 3^k
      -- From hkey : 3^k - 4^l = 4^l * (exp δ₁ - 1), so 3^k = 4^l * exp δ₁.
      have h3_eq : (3 : ℝ)^k = (4 : ℝ)^l * Real.exp δ₁ := by linarith [hkey]
      rw [h3_eq]
      -- Goal: 4^l * (1 - exp δ₁) * 3 < 4^l * exp δ₁
      rw [mul_assoc]  -- 4^l * (1 - exp) * 3 → 4^l * ((1 - exp) * 3)
      rw [mul_lt_mul_iff_right₀ h4_pos_real]
      -- Goal: (1 - exp δ₁) * 3 < exp δ₁
      rw [sub_mul]
      rw [gt_iff_lt] at hexp_δ₁_gt_3_4
      linarith [hexp_δ₁_gt_3_4]
    -- Wrap up the integer goal.
    -- Goal: |((3 : ℤ)^(n.natAbs) - (4 : ℤ)^(m.natAbs) : ℤ)| * 3
    --       < (min ((3 : ℕ)^(n.natAbs)) ((4 : ℕ)^(m.natAbs)) : ℤ)
    -- Step 1: Convert n.natAbs → k, m.natAbs → l.
    have e1 : (3 : ℤ)^n.natAbs = (3 : ℤ)^k := by simp only [k]
    have e2 : (4 : ℤ)^m.natAbs = (4 : ℤ)^l := by simp only [l]
    rw [e1, e2]
    -- Step 2: Drop redundant `(... : ℤ)` cast on the abs arg.
    have e_abs : ((3 : ℤ)^k - (4 : ℤ)^l : ℤ) = ((3 : ℤ)^k - (4 : ℤ)^l) := rfl
    rw [e_abs]
    -- Goal: |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (min ((3 : ℕ)^k) ((4 : ℕ)^l) : ℤ)
    -- Step 3: Convert RHS min to (3 : ℤ)^k.
    have hmin_eq : (min ((3 : ℕ)^k) ((4 : ℕ)^l) : ℤ) = (3 : ℤ)^k := by
      apply @min_eq_left (α := ℤ) _ (↑(3^k)) (↑(4^l))
      -- ↑(3^k) ≤ ↑(4^l) follows from h3_lt_4.
      exact_mod_cast h3_lt_4.le
    rw [hmin_eq]
    -- Goal: |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (3 : ℤ)^k
    -- Step 4: Lift hmul (ℝ inequality) to ℤ.
    have hmul_ℤ : |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (3 : ℤ)^k := by
      exact_mod_cast hmul
    exact hmul_ℤ
  · -- Case 2: 3^k ≥ 4^l, so min = 4^l.
    -- We need: 4^l · |exp δ₁ - 1| · 3 < 4^l, i.e., |exp δ₁ - 1| < 1/3.
    -- Goal in reals: 4^l * |exp δ₁ - 1| * 3 < 4^l.
    have hmul : (4 : ℝ)^l * |Real.exp δ₁ - 1| * 3 < (4 : ℝ)^l := by
      have h1 : (4 : ℝ)^l * |Real.exp δ₁ - 1| < (4 : ℝ)^l * (1/3) :=
        mul_lt_mul_of_pos_left hexp_δ₁_lt h4_pos_real
      linarith
    -- Convert back to integers.
    refine ⟨(n : ℤ), (m : ℤ), ?_⟩
    -- Goal: |((3 : ℤ)^(n.natAbs) - (4 : ℤ)^(m.natAbs) : ℤ)| * 3
    --       < (min ((3 : ℕ)^(n.natAbs)) ((4 : ℕ)^(m.natAbs)) : ℤ)
    -- Step 1: Convert n.natAbs → k, m.natAbs → l.
    have e1 : (3 : ℤ)^n.natAbs = (3 : ℤ)^k := by simp only [k]
    have e2 : (4 : ℤ)^m.natAbs = (4 : ℤ)^l := by simp only [l]
    rw [e1, e2]
    -- Step 2: Drop redundant `(... : ℤ)` cast on the abs arg.
    have e_abs : ((3 : ℤ)^k - (4 : ℤ)^l : ℤ) = ((3 : ℤ)^k - (4 : ℤ)^l) := rfl
    rw [e_abs]
    -- Goal: |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (min ((3 : ℕ)^k) ((4 : ℕ)^l) : ℤ)
    -- Step 3: Convert RHS min to (4 : ℤ)^l. Note: (4:ℤ)^l ≤ (3:ℤ)^k in ℤ follows from h3_ge_4.
    have hmin_eq : (min ((3 : ℕ)^k) ((4 : ℕ)^l) : ℤ) = (4 : ℤ)^l := by
      apply @min_eq_right (α := ℤ) _ (↑(3^k)) (↑(4^l))
      -- ↑(4^l) ≤ ↑(3^k) follows from h3_ge_4.
      exact_mod_cast h3_ge_4
    rw [hmin_eq]
    -- Goal: |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (4 : ℤ)^l
    -- Step 4: Lift hmul (ℝ inequality) to ℤ.
    have hmul_ℤ : |(3 : ℤ)^k - (4 : ℤ)^l| * 3 < (4 : ℤ)^l := by
      have hreal : (|(3 : ℤ)^k - (4 : ℤ)^l| : ℝ) * 3 < (4 : ℝ)^l := by
        have cast_abs : (|(3 : ℤ)^k - (4 : ℤ)^l| : ℝ) = |(3 : ℝ)^k - (4 : ℝ)^l| := by
          simp [Int.cast_sub, Int.cast_abs]
        rw [cast_abs, habs]
        exact hmul
      exact_mod_cast hreal
    exact hmul_ℤ
