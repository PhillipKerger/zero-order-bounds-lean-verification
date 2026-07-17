import ZeroOrderBounds.OracleState
import ZeroOrderBounds.ProjectionGeometry

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Public vocabulary for the improved-accuracy lower bound

This module deliberately imports no proof of the new lower bound.  It is the
trusted statement boundary used by Comparator.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- The paper's explicit `10⁻⁷ / sqrt d` accuracy in even dimension
`d = 2m`. -/
def sqrtAccuracy (m : ℕ) : ℝ :=
  1 / (10000000 * Real.sqrt (2 * (m : ℝ)))

/-- A fixed-horizon strategy succeeds uniformly at the improved accuracy. -/
def SucceedsWithinSqrt (m T : ℕ) [NeZero m] : Prop :=
  ∃ A : DeterministicStrategy m,
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = T →
      Admissible W →
      Consistent A ys W →
      hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) ≤ sqrtAccuracy m

end ZeroOrderBounds.AccuracyImprovement
