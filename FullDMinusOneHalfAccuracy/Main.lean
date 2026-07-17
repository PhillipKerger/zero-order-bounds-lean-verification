import FullDMinusOneHalfAccuracy.BrunnMinkowskiInduction
import FullDMinusOneHalfAccuracy.ComplexityBridge

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Unconditional `d⁻¹ᵗ²` zero-order lower bound

This is the production endpoint of the improved-accuracy formalization.  The
Euclidean Brunn--Minkowski family proved by dimension induction discharges the
last geometric hypothesis of `MainBridge`.  The remaining declarations state
the corresponding fixed-horizon, stopping-strategy, and explicit integer-
budget consequences without geometric premises.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- The unconditional fixed-horizon theorem, with exactly the conclusion and
horizon normalization of the trusted Comparator challenge. -/
theorem fixedHorizonSqrtLowerBound_strict
    {m T : ℕ} [NeZero m]
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 /
        Real.log (Real.exp 1 * (m : ℝ)))
    (A : ZeroOrderBounds.DeterministicStrategy m) :
    ∃ ys : List ℝ, ∃ W : ZeroOrderBounds.RowMatrix m,
      ys.length = T ∧
      ZeroOrderBounds.Admissible W ∧
      ZeroOrderBounds.hardObjective W 0 = 0 ∧
      ConvexOn ℝ Set.univ (ZeroOrderBounds.hardObjective W) ∧
      LipschitzWith 1 (ZeroOrderBounds.hardObjective W) ∧
      ZeroOrderBounds.Consistent A ys W ∧
      ZeroOrderBounds.hardOptimizer W ∈ ZeroOrderBounds.unitBall m ∧
      IsMinOn (ZeroOrderBounds.hardObjective W) (ZeroOrderBounds.unitBall m)
        (ZeroOrderBounds.hardOptimizer W) ∧
      sqrtAccuracy m <
        ZeroOrderBounds.hardObjective W
            (A.output ys : ZeroOrderBounds.QuerySpace m) -
          ZeroOrderBounds.hardObjective W
            (ZeroOrderBounds.hardOptimizer W) := by
  apply fixedHorizonSqrtLowerBound_strict_of_euclidean_brunnMinkowski
    euclidean_brunnMinkowski_family
  simpa only [paperLog] using horizon

/-- No deterministic fixed-horizon strategy succeeds below the real paper
threshold. -/
theorem not_succeedsWithinSqrt
    {m T : ℕ} [NeZero m]
    (horizon : (T : ℝ) ≤ paperQueryThreshold m) :
    ¬ SucceedsWithinSqrt m T :=
  not_succeedsWithinSqrt_of_euclidean_brunnMinkowski
    euclidean_brunnMinkowski_family horizon

/-- Every integer horizon at most the floored paper budget is impossible for
fixed-horizon deterministic strategies. -/
theorem not_succeedsWithinSqrt_of_le_paperQueryBudget
    {m T : ℕ} [NeZero m] (hT : T ≤ paperQueryBudget m) :
    ¬ SucceedsWithinSqrt m T :=
  not_succeedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
    euclidean_brunnMinkowski_family hT

/-- The same integer-budget impossibility for transcript-dependent strategies
which may stop at any time up to `T`. -/
theorem not_atMostSucceedsWithinSqrt_of_le_paperQueryBudget
    {m T : ℕ} [NeZero m] (hT : T ≤ paperQueryBudget m) :
    ¬ StoppingStrategy.AtMostSucceedsWithin m T (sqrtAccuracy m) :=
  not_atMostSucceedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
    euclidean_brunnMinkowski_family hT

/-- In particular, no stopping strategy succeeds at the canonical floored
paper budget. -/
theorem not_atMostPaperQueryBudgetSucceedsWithinSqrt
    {m : ℕ} [NeZero m] :
    ¬ StoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
      (sqrtAccuracy m) :=
  not_atMostPaperQueryBudgetSucceedsWithinSqrt_of_euclidean_brunnMinkowski
    euclidean_brunnMinkowski_family

/-- Literal even-dimensional rate: the first integer outside the ruled-out
budget is greater than `d² / (800 log(d+1))`, for `d = 2m`. -/
theorem paperQueryBudget_succ_gt_even_dimension_log_succ_rate
    {m : ℕ} (hm : 0 < m) :
    (2 * (m : ℝ)) ^ 2 /
        (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) <
      ((paperQueryBudget m + 1 : ℕ) : ℝ) :=
  even_dimension_log_succ_rate_lt_budget_succ hm

/-- Audit-friendly combined complexity statement: the canonical budget is
impossible and its successor dominates the explicit quadratic-over-log rate. -/
theorem not_atMostPaperQueryBudgetSucceedsWithinSqrt_and_rate
    {m : ℕ} [NeZero m] :
    (¬ StoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
        (sqrtAccuracy m)) ∧
      (2 * (m : ℝ)) ^ 2 /
          (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) <
        ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact ⟨not_atMostPaperQueryBudgetSucceedsWithinSqrt,
    paperQueryBudget_succ_gt_even_dimension_log_succ_rate
      (Nat.pos_of_ne_zero (NeZero.ne m))⟩

end ZeroOrderBounds.AccuracyImprovement
