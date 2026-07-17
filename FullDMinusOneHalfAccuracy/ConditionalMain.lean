import FullDMinusOneHalfAccuracy.FinalAssembly
import FullDMinusOneHalfAccuracy.ManyGoodRows
import FullDMinusOneHalfAccuracy.RowProjectionBridge

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# End-to-end assembly from the intrinsic Urysohn certificate

This module records the complete optimization proof with the sole remaining
geometric input displayed as an ordinary explicit hypothesis.  The production
`Main` theorem will discharge that hypothesis using the trust-zero Urysohn
module; no final public theorem is allowed to retain it.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- The resisting-oracle, projection, common-direction, and separation chain
from the precise row-level consequence of intrinsic Urysohn. -/
theorem fixedHorizonLowerBound_strict_of_intrinsic_urysohn
    {m T : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m)
    (hurysohn : ∀ (P : RowBody m) (hdim : 0 < P.dim),
      (1 / 2 : ℝ) <
          P.normalizedVolume ^ (((P.dim : ℕ) : ℝ)⁻¹) →
        tau m ≤ positiveIntrinsicMeanWidth P hdim) :
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
  obtain ⟨G, _hhalf, hcard, hgood⟩ :=
    oracleRun_many_good_rows (T := T) A horizon
  let rows : Fin m → RowBody m := (oracleStateAt A T).rows
  have hdim : ∀ i ∈ G, 24 * m ≤ 25 * (rows i).dim := by
    intro i hi
    exact (hgood i hi).2.1
  have hdim_pos : ∀ i ∈ G, 0 < (rows i).dim := by
    intro i hi
    exact (hgood i hi).2.2.1
  have hwidth : ∀ i, ∀ hi : i ∈ G,
      tau m ≤ positiveIntrinsicMeanWidth (rows i) (hdim_pos i hi) := by
    intro i hi
    apply hurysohn (rows i) (hdim_pos i hi)
    exact (hgood i hi).2.2.2.2
  have hmean : ∀ i ∈ G,
      tau m / 2 ≤ sphericalMeanWidth (rows i : Set (RowSpace m)) :=
    row_meanWidths_of_intrinsic_meanWidths rows G hdim hdim_pos hwidth
  apply fixedHorizonLowerBound_strict_of_row_meanWidths A G hcard
  simpa [rows] using hmean

end ZeroOrderBounds.AccuracyImprovement
