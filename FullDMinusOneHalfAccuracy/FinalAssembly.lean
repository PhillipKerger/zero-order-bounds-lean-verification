import FullDMinusOneHalfAccuracy.WidthEndgame
import ZeroOrderBounds.OracleRun

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Optimization endpoint from certified row mean widths

The theorem in this file is the final consumer of convex geometry.  It exposes
the complete audit-facing lower-bound witness while taking only the precise
row mean-width certificates that `Urysohn` and `SphericalProjection` must
eventually supply.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- Full fixed-horizon lower-bound conclusion from a half-sized collection of
final rows with ambient mean width at least `tau/2`. -/
theorem fixedHorizonLowerBound_strict_of_row_meanWidths
    {m T : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (G : Finset (Fin m)) (hcard : m ≤ 2 * G.card)
    (hmean : ∀ i ∈ G,
      tau m / 2 ≤ sphericalMeanWidth
        ((oracleStateAt A T).rows i : Set (RowSpace m))) :
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
  let S : OracleState A := oracleStateAt A T
  obtain ⟨W, hW, hconsistent, hgap⟩ :=
    OracleState.exists_consistent_selection_with_sqrt_gap_of_row_meanWidths
      S G hcard (by simpa [S] using hmean)
  have hAdmissible : Admissible W := admissible_of_mem_rowProduct hW
  refine ⟨S.answers, W, ?_, hAdmissible, hardObjective_zero W,
    convexOn_hardObjective W, hardObjective_lipschitzWith_one W hAdmissible,
    hconsistent, hardOptimizer_mem_unitBall W, hardOptimizer_isMinOn W, hgap⟩
  simp [S]

end ZeroOrderBounds.AccuracyImprovement
