import FullDMinusOneHalfAccuracy.AggregateSeparation
import FullDMinusOneHalfAccuracy.CommonDirection
import FullDMinusOneHalfAccuracy.Numerics
import ZeroOrderBounds.FinalGap

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Mean widths to an indistinguishable hard instance

This file closes the optimization-specific part of the improved-accuracy
argument.  Its only geometric input is an ambient spherical mean-width bound
for each row in a finset containing at least half the rows.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds.AccuracyImprovement

/-- Mean width `tau/2` on at least half the final row bodies yields two
transcript-compatible product selections whose optimizers are more than
`1/600` apart. -/
theorem OracleState.exists_pair_optimizer_separated_of_row_meanWidths
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) (G : Finset (Fin m))
    (hcard : m ≤ 2 * G.card)
    (hmean : ∀ i ∈ G,
      tau m / 2 ≤
        sphericalMeanWidth (S.rows i : Set (RowSpace m))) :
    ∃ Wplus Wminus : RowMatrix m,
      Wplus ∈ rowProduct S.rows ∧
      Wminus ∈ rowProduct S.rows ∧
      Consistent A S.answers Wplus ∧
      Consistent A S.answers Wminus ∧
      1 / 600 < ‖hardOptimizer Wplus - hardOptimizer Wminus‖ := by
  obtain ⟨θ, hθ, haggregate⟩ :=
    exists_common_direction_of_row_meanWidth S.rows G hcard hmean
  obtain ⟨Wplus, Wminus, hplus, hminus, _hagree, _hwidth,
      _hrowMean, _hzBlock, _hminPoint, hoptimizer⟩ :=
    exists_aggregate_separated_matrices S.rows G θ hθ haggregate
  exact ⟨Wplus, Wminus, hplus, hminus,
    S.every_selection_consistent hplus,
    S.every_selection_consistent hminus, hoptimizer⟩

/-- The separated pair defeats the deterministic strategy at the advertised
`10⁻⁷/sqrt(2m)` accuracy on one exact-transcript-compatible selection. -/
theorem OracleState.exists_consistent_selection_with_sqrt_gap_of_row_meanWidths
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) (G : Finset (Fin m))
    (hcard : m ≤ 2 * G.card)
    (hmean : ∀ i ∈ G,
      tau m / 2 ≤
        sphericalMeanWidth (S.rows i : Set (RowSpace m))) :
    ∃ W : RowMatrix m,
      W ∈ rowProduct S.rows ∧
      Consistent A S.answers W ∧
      sqrtAccuracy m <
        hardObjective W (A.output S.answers : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  obtain ⟨Wplus, Wminus, hplus, hminus, hconsistentPlus,
      hconsistentMinus, hsep⟩ :=
    OracleState.exists_pair_optimizer_separated_of_row_meanWidths
      S G hcard hmean
  have hq : (A.output S.answers : QuerySpace m) ∈ unitBall m :=
    A.output_mem_unitBall S.answers
  have hgap := one_of_two_objective_gaps Wplus Wminus hq
    (show (0 : ℝ) ≤ 1 / 600 by norm_num) hsep.le
  have hnumeric : sqrtAccuracy m <
      a / (8 * Real.sqrt (m : ℝ)) * (1 / 600 : ℝ) ^ 2 := by
    simpa [advertisedSqrtAccuracy] using
      advertisedSqrtAccuracy_lt_one_div_six_hundred_growth (m := m)
  rcases hgap with hgap | hgap
  · exact ⟨Wplus, hplus, hconsistentPlus, hnumeric.trans_le hgap⟩
  · exact ⟨Wminus, hminus, hconsistentMinus, hnumeric.trans_le hgap⟩

end ZeroOrderBounds.AccuracyImprovement
