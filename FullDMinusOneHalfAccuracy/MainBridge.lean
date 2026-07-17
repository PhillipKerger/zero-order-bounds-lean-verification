import FullDMinusOneHalfAccuracy.ConditionalMain
import FullDMinusOneHalfAccuracy.RowUrysohnConsequence

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Final bridge from Euclidean Brunn--Minkowski to the optimization theorem

This file fixes the exact public interface expected from the dimension
induction.  Once Brunn--Minkowski is available in every positive standard
Euclidean dimension, all row-specific Urysohn premises and hence the full
fixed-horizon lower bound follow without any further geometry.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- End-to-end lower bound from the dimension-uniform Euclidean
Brunn--Minkowski theorem.  The eventual production `Main` theorem supplies
`hBM` using the trust-zero induction module. -/
theorem fixedHorizonSqrtLowerBound_strict_of_euclidean_brunnMinkowski
    {m T : ℕ} [NeZero m]
    (hBM : ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ)
        (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m)
    (A : DeterministicStrategy m) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      hardObjective W 0 = 0 ∧
      ConvexOn ℝ Set.univ (hardObjective W) ∧
      LipschitzWith 1 (hardObjective W) ∧
      Consistent A ys W ∧
      hardOptimizer W ∈ unitBall m ∧
      IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) ∧
      sqrtAccuracy m <
        hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  apply fixedHorizonLowerBound_strict_of_intrinsic_urysohn A horizon
  intro P hdim hradius
  apply tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius
    P hdim _ hradius
  intro K L
  have hn : 0 < Module.finrank ℝ P.body.directionSpan := by
    rw [finrank_directionSpan_eq_dim]
    exact hdim
  exact hBM (Module.finrank ℝ P.body.directionSpan) hn
    (1 / 2 : ℝ) K L (by norm_num) (by norm_num)

end ZeroOrderBounds.AccuracyImprovement
