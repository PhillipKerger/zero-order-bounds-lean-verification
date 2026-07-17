import FullDMinusOneHalfAccuracy.Numerics
import Mathlib.Analysis.Complex.ExponentialBounds

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Integer query budget at the paper threshold

The resisting-oracle theorem is naturally stated for every real-valued
horizon below `m² / (100 log (e m))`.  This file packages the integer floor
used in the paper and records an explicit quadratic-over-logarithmic lower
bound in the even ambient dimension `d = 2m`.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- The real query threshold in the proof, before taking an integer floor. -/
def paperQueryThreshold (m : ℕ) : ℝ :=
  (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m

/-- The largest integer horizon automatically covered by the paper
threshold. -/
def paperQueryBudget (m : ℕ) : ℕ :=
  ⌊paperQueryThreshold m⌋₊

theorem paperQueryThreshold_nonneg {m : ℕ} (hm : 0 < m) :
    0 ≤ paperQueryThreshold m := by
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg (m : ℝ)))
    (paperLog_pos hm).le

/-- The floored budget satisfies the horizon hypothesis consumed by the
fixed-horizon lower bound. -/
theorem paperQueryBudget_le_threshold {m : ℕ} (hm : 0 < m) :
    (paperQueryBudget m : ℝ) ≤ paperQueryThreshold m := by
  exact Nat.floor_le (paperQueryThreshold_nonneg hm)

theorem horizon_of_le_paperQueryBudget {m T : ℕ} (hm : 0 < m)
    (hT : T ≤ paperQueryBudget m) :
    (T : ℝ) ≤ (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m := by
  rw [← paperQueryThreshold]
  have hTR : (T : ℝ) ≤ (paperQueryBudget m : ℝ) := by
    exact_mod_cast hT
  exact hTR.trans (paperQueryBudget_le_threshold hm)

/-- As usual for a floor, the first integer not ruled out is strictly above
the real threshold. -/
theorem paperQueryThreshold_lt_budget_succ (m : ℕ) :
    paperQueryThreshold m < ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  simpa [paperQueryBudget] using Nat.lt_floor_add_one (paperQueryThreshold m)

/-- Monotonicity of the logarithmic denominator on positive natural
arguments. -/
theorem paperLog_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    paperLog m ≤ paperLog n := by
  rw [paperLog, paperLog]
  apply Real.log_le_log
  · exact mul_pos (Real.exp_pos 1) (by exact_mod_cast hm)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (Real.exp_pos 1).le

/-- The real threshold is already an explicit quadratic-over-logarithmic
quantity in the even ambient dimension `d = 2m`.  The denominator
`paperLog (2m) = log (e d)` is a harmless standard `log(d+1)` surrogate. -/
theorem even_dimension_rate_le_paperQueryThreshold {m : ℕ} (hm : 0 < m) :
    (1 / 400 : ℝ) * (2 * (m : ℝ)) ^ 2 / paperLog (2 * m) ≤
      paperQueryThreshold m := by
  have h2m : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hmono : paperLog m ≤ paperLog (2 * m) :=
    paperLog_mono hm (by omega)
  have hnum :
      (1 / 400 : ℝ) * (2 * (m : ℝ)) ^ 2 =
        (1 / 100 : ℝ) * (m : ℝ) ^ 2 := by
    ring
  rw [paperQueryThreshold, hnum]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num) (sq_nonneg (m : ℝ)))
    (paperLog_pos hm) hmono

/-- Consequently the first integer beyond the ruled-out range is strictly
larger than an explicit `d² / log(e d)` expression. -/
theorem even_dimension_rate_lt_budget_succ {m : ℕ} (hm : 0 < m) :
    (1 / 400 : ℝ) * (2 * (m : ℝ)) ^ 2 / paperLog (2 * m) <
      ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact (even_dimension_rate_le_paperQueryThreshold hm).trans_lt
    (paperQueryThreshold_lt_budget_succ m)

/-- The paper logarithm in even dimension is at most twice the conventional
`log (d + 1)` denominator. -/
theorem paperLog_even_le_two_log_succ {m : ℕ} (hm : 0 < m) :
    paperLog (2 * m) ≤
      2 * Real.log ((2 * m + 1 : ℕ) : ℝ) := by
  have h2m : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have h2mR : (0 : ℝ) < (2 * m : ℕ) := by
    exact_mod_cast h2m
  have hcast_le : ((2 * m : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ (2 * m))
  have hlogMono :
      Real.log ((2 * m : ℕ) : ℝ) ≤
        Real.log ((2 * m + 1 : ℕ) : ℝ) :=
    Real.log_le_log h2mR hcast_le
  have hthree : 3 ≤ 2 * m + 1 := by omega
  have hthreeR : (3 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hthree
  have hexp : Real.exp 1 ≤ ((2 * m + 1 : ℕ) : ℝ) :=
    (le_of_lt Real.exp_one_lt_three).trans hthreeR
  have hone : 1 ≤ Real.log ((2 * m + 1 : ℕ) : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp
  rw [paperLog_eq_one_add_log h2m]
  linarith

/-- Literal paper-rate form: in even dimension `d = 2m`, the first integer
not ruled out is larger than `d² / (800 log(d+1))`. -/
theorem even_dimension_log_succ_rate_lt_budget_succ {m : ℕ} (hm : 0 < m) :
    (2 * (m : ℝ)) ^ 2 /
        (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) <
      ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  have h2m : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hpaper : 0 < paperLog (2 * m) := paperLog_pos h2m
  have hlog : 0 < Real.log ((2 * m + 1 : ℕ) : ℝ) := by
    have hone : (1 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 < 2 * m + 1)
    exact Real.log_pos hone
  have hden :
      400 * paperLog (2 * m) ≤
        800 * Real.log ((2 * m + 1 : ℕ) : ℝ) := by
    nlinarith [paperLog_even_le_two_log_succ hm]
  have hcompare :
      (2 * (m : ℝ)) ^ 2 /
          (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) ≤
        (2 * (m : ℝ)) ^ 2 / (400 * paperLog (2 * m)) := by
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (mul_pos (by norm_num) hpaper) hden
  have hrate := even_dimension_rate_lt_budget_succ hm
  have hrewrite :
      (2 * (m : ℝ)) ^ 2 / (400 * paperLog (2 * m)) =
        (1 / 400 : ℝ) * (2 * (m : ℝ)) ^ 2 / paperLog (2 * m) := by
    ring
  rw [hrewrite] at hcompare
  exact hcompare.trans_lt hrate

end ZeroOrderBounds.AccuracyImprovement
