import FullDMinusOneHalfAccuracy.MainBridge
import FullDMinusOneHalfAccuracy.QueryBudget
import FullDMinusOneHalfAccuracy.StoppingStrategy

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Query-complexity consequences of the improved fixed-horizon lower bound

This file is the public complexity-theoretic bridge.  It combines the
certificate-producing fixed-horizon theorem in `MainBridge` with the integer
budget in `QueryBudget` and the exact padding equivalence in
`StoppingStrategy`.

The sole geometric premise is dimension-uniform Euclidean
Brunn--Minkowski—the same premise exposed by `MainBridge`.  In particular,
the stopping-strategy statements below introduce no new geometric or analytic
assumptions.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

open ZeroOrderBounds

/-- No fixed-horizon deterministic strategy succeeds at the paper's
`d⁻¹ᐟ²` accuracy whenever its horizon is below the real query threshold.

This is the logical negation of the existential success predicate in
`Statement.lean`; the strict counterexample supplied by `MainBridge`
contradicts its non-strict success guarantee. -/
theorem not_succeedsWithinSqrt_of_euclidean_brunnMinkowski
    {m T : ℕ} [NeZero m]
    (hBM : ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ)
        (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L)
    (horizon : (T : ℝ) ≤ paperQueryThreshold m) :
    ¬ SucceedsWithinSqrt m T := by
  intro hsuccess
  obtain ⟨A, hA⟩ := hsuccess
  obtain ⟨ys, W, hlen, hW, _, _, _, hconsistent, _, _, hgap⟩ :=
    fixedHorizonSqrtLowerBound_strict_of_euclidean_brunnMinkowski
      hBM (by simpa [paperQueryThreshold] using horizon) A
  exact (not_lt_of_ge (hA ys W hlen hW hconsistent)) hgap

/-- Every integer horizon at most the floored paper budget is impossible at
the improved accuracy. -/
theorem not_succeedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
    {m T : ℕ} [NeZero m]
    (hBM : ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ)
        (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L)
    (hT : T ≤ paperQueryBudget m) :
    ¬ SucceedsWithinSqrt m T := by
  apply not_succeedsWithinSqrt_of_euclidean_brunnMinkowski hBM
  exact horizon_of_le_paperQueryBudget
    (Nat.pos_of_ne_zero (NeZero.ne m)) hT

/-- More strongly, for every horizon at most the paper budget, even a
transcript-dependent strategy which may stop early cannot succeed. -/
theorem not_atMostSucceedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
    {m T : ℕ} [NeZero m]
    (hBM : ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ)
        (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L)
    (hT : T ≤ paperQueryBudget m) :
    ¬ StoppingStrategy.AtMostSucceedsWithin m T (sqrtAccuracy m) := by
  exact StoppingStrategy.not_atMostSucceedsWithinSqrt_of_not_succeedsWithinSqrt
    (not_succeedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
      hBM hT)

/-- At the canonical floored budget, no transcript-dependent at-most-budget
strategy succeeds at the improved accuracy. -/
theorem not_atMostPaperQueryBudgetSucceedsWithinSqrt_of_euclidean_brunnMinkowski
    {m : ℕ} [NeZero m]
    (hBM : ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ)
        (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L) :
    ¬ StoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
        (sqrtAccuracy m) := by
  exact
    not_atMostSucceedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
      hBM le_rfl

/-- The first integer horizon not covered by the lower bound is strictly
larger than the clean even-dimensional rate
`(2m)² / (400 log(e·2m))`. -/
theorem paperQueryBudget_succ_gt_even_dimension_rate
    {m : ℕ} (hm : 0 < m) :
    (2 * (m : ℝ)) ^ 2 / (400 * paperLog (2 * m)) <
      ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  have hrate_eq :
      (2 * (m : ℝ)) ^ 2 / (400 * paperLog (2 * m)) =
        (1 / 400 : ℝ) * (2 * (m : ℝ)) ^ 2 / paperLog (2 * m) := by
    ring
  rw [hrate_eq]
  exact even_dimension_rate_lt_budget_succ hm

#print axioms not_succeedsWithinSqrt_of_euclidean_brunnMinkowski
#print axioms not_atMostPaperQueryBudgetSucceedsWithinSqrt_of_euclidean_brunnMinkowski
#print axioms not_succeedsWithinSqrt_of_le_paperQueryBudget_of_euclidean_brunnMinkowski
#print axioms paperQueryBudget_succ_gt_even_dimension_rate

end ZeroOrderBounds.AccuracyImprovement
