import ZeroOrderBounds.GoodRow
import FullDMinusOneHalfAccuracy.Statement
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Numerical estimates for the improved-accuracy argument

This file isolates the logarithmic estimates used by the many-good-rows
argument.  The query horizon is measured using `paperLog m = log (e * m)`.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- The positive logarithm occurring in the paper-scale query horizon. -/
def paperLog (m : ℕ) : ℝ :=
  Real.log (Real.exp 1 * (m : ℝ))

theorem paperLog_eq_one_add_log {m : ℕ} (hm : 0 < m) :
    paperLog m = 1 + Real.log (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [paperLog, Real.log_mul (Real.exp_ne_zero 1) hmR, Real.log_exp]

theorem one_le_paperLog {m : ℕ} (hm : 0 < m) :
    1 ≤ paperLog m := by
  rw [paperLog_eq_one_add_log hm]
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact le_add_of_nonneg_right (Real.log_nonneg hmR)

theorem paperLog_pos {m : ℕ} (hm : 0 < m) :
    0 < paperLog m :=
  lt_of_lt_of_le zero_lt_one (one_le_paperLog hm)

/-- A convenient rigorous bound on the fixed constant in `entropyScale`. -/
theorem log_sixtyfour_thirds_le_four :
    Real.log (64 / 3 : ℝ) ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 64 / 3)]
  have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 5
  norm_num at h ⊢
  linarith

/-- The current oracle entropy loss is at most four paper logarithms.
This is the constant needed for the `1/100` horizon and the `1/6`
per-surviving-dimension entropy bound. -/
theorem entropyScale_le_four_paperLog {m : ℕ} (hm : 0 < m) :
    entropyScale m ≤ 4 * paperLog m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from hm))
  rw [entropyScale, Real.log_mul (mul_ne_zero (by norm_num) hmR.ne') hsqrt.ne',
    Real.log_mul (by norm_num : (64 / 3 : ℝ) ≠ 0) hmR.ne',
    Real.log_sqrt hmR.le, paperLog_eq_one_add_log hm]
  nlinarith [log_sixtyfour_thirds_le_four]

/-- Clearing the positive paper logarithm from the horizon. -/
theorem paper_horizon_mul_log_le_square {m T : ℕ} (hm : 0 < m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    100 * (T : ℝ) * paperLog m ≤ (m : ℝ) ^ 2 := by
  have hlog := paperLog_pos hm
  rw [le_div_iff₀ hlog] at horizon
  nlinarith

/-- The paper horizon alone bounds the total codimension budget. -/
theorem hundred_mul_horizon_le_square {m T : ℕ} (hm : 0 < m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    100 * (T : ℝ) ≤ (m : ℝ) ^ 2 := by
  have hcleared := paper_horizon_mul_log_le_square hm horizon
  have hlog := one_le_paperLog hm
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hcompare : 100 * (T : ℝ) ≤ 100 * (T : ℝ) * paperLog m := by
    have := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ 100 * (T : ℝ) by positivity)
    nlinarith
  exact hcompare.trans hcleared

/-- The paper horizon pays for twenty-five copies of the current entropy
loss scale. -/
theorem twentyfive_mul_horizon_entropyScale_le_square {m T : ℕ}
    (hm : 0 < m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    25 * (T : ℝ) * entropyScale m ≤ (m : ℝ) ^ 2 := by
  have hcleared := paper_horizon_mul_log_le_square hm horizon
  have hscale := entropyScale_le_four_paperLog hm
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hmul := mul_le_mul_of_nonneg_left hscale hT
  nlinarith

/-- `exp (-1/6)` is strictly larger than one half. -/
theorem one_half_lt_exp_neg_one_sixth :
    (1 / 2 : ℝ) < Real.exp (-(1 : ℝ) / 6) := by
  have hlinear := Real.add_one_le_exp (-(1 : ℝ) / 6)
  norm_num at hlinear ⊢
  linarith

/-! ## Final `d⁻¹ᐟ²` accuracy constants -/

/-- The advertised accuracy in ambient dimension `d = 2m`. -/
def advertisedSqrtAccuracy (m : ℕ) : ℝ :=
  sqrtAccuracy m

/-- Optimizer separation `1/600` gives the paper's explicit quadratic-growth
coefficient. -/
theorem one_div_six_hundred_growth_eq {m : ℕ} [NeZero m] :
    a / (8 * Real.sqrt (m : ℝ)) * (1 / 600 : ℝ) ^ 2 =
      1 / (5760000 * Real.sqrt (m : ℝ)) := by
  rw [a]
  ring

/-- The explicit growth coefficient is strictly larger than
`10⁻⁷ / sqrt (2m)`. -/
theorem advertisedSqrtAccuracy_lt_one_div_six_hundred_growth
    {m : ℕ} [NeZero m] :
    advertisedSqrtAccuracy m <
      a / (8 * Real.sqrt (m : ℝ)) * (1 / 600 : ℝ) ^ 2 := by
  rw [one_div_six_hundred_growth_eq]
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hsle : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (m : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  unfold advertisedSqrtAccuracy sqrtAccuracy
  apply one_div_lt_one_div_of_lt
  · positivity
  · nlinarith

end ZeroOrderBounds.AccuracyImprovement
