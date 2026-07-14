import ZeroOrderBounds.OracleState
import ZeroOrderBounds.OneRowSensitivity
import ZeroOrderBounds.FinalGap

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Two indistinguishable final instances

This module is independent of how the resisting-oracle state was reached.  A
pair of points in one final row body extends to two matrices in the maintained
Cartesian product.  The product invariant gives the same exact transcript for
both matrices; one-row sensitivity and quadratic growth then force one of the
two objectives to have a large error at the deterministic strategy's common
output.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds

/-- Extend two choices in one row body to two product selections which agree
on every other row. -/
theorem exists_product_selections_perturbRow {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (i : Fin m)
    {w w' : RowSpace m} (hw : w ∈ rows i) (hw' : w' ∈ rows i) :
    ∃ W : RowMatrix m,
      W ∈ rowProduct rows ∧
      perturbRow W i (w' - w) ∈ rowProduct rows ∧
      W i = w ∧ perturbRow W i (w' - w) i = w' := by
  classical
  obtain ⟨W₀, hW₀⟩ := rowProduct_nonempty rows
  let W : RowMatrix m := Function.update W₀ i w
  have hW : W ∈ rowProduct rows := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [W]
    · simpa [W, hji] using hW₀ j
  have hWi : W i = w := by simp [W]
  have hpert_i : perturbRow W i (w' - w) i = w' := by
    simp [hWi]
  have hpert : perturbRow W i (w' - w) ∈ rowProduct rows := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [hWi] using hw'
    · rw [perturbRow_of_ne W i j (w' - w) hji]
      exact hW j
  exact ⟨W, hW, hpert, hWi, hpert_i⟩

/-- A separated pair in one final row forces a sensitivity-scale objective gap
on one transcript-compatible selection. -/
theorem OracleState.exists_consistent_selection_with_gap_of_pair
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) (i : Fin m)
    {w w' : RowSpace m} (hw : w ∈ S.rows i) (hw' : w' ∈ S.rows i) :
    ∃ W : RowMatrix m,
      W ∈ rowProduct S.rows ∧
      Consistent A S.answers W ∧
      ‖w' - w‖ ^ 2 /
          (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) ≤
        hardObjective W (A.output S.answers : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  obtain ⟨W, hW, hW', hWi, hW'i⟩ :=
    exists_product_selections_perturbRow S.rows i hw hw'
  let W' := perturbRow W i (w' - w)
  have hAdm : Admissible W := admissible_of_mem_rowProduct hW
  have hAdm' : Admissible W' := admissible_of_mem_rowProduct hW'
  have hsep : ‖w' - w‖ / (16 * a * Real.sqrt (m : ℝ)) ≤
      ‖hardOptimizer W - hardOptimizer W'‖ :=
    hardOptimizer_perturbRow_separation W i (w' - w) hAdm hAdm'
  have hq : (A.output S.answers : QuerySpace m) ∈ unitBall m :=
    A.output_mem_unitBall S.answers
  have hgap := one_of_two_objective_gaps_of_sensitivity_scale W W' hq
    (norm_nonneg (w' - w)) hsep
  rcases hgap with hgap | hgap
  · exact ⟨W, hW, S.every_selection_consistent hW, hgap⟩
  · exact ⟨W', hW', S.every_selection_consistent hW', hgap⟩

/-- Quarter-power separation gives the advertised strict error on one fixed,
transcript-compatible hard instance. -/
theorem OracleState.exists_consistent_selection_with_advertised_gap
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) (i : Fin m)
    {w w' : RowSpace m} (hw : w ∈ S.rows i) (hw' : w' ∈ S.rows i)
    (hsep : tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4) ≤ dist w w') :
    ∃ W : RowMatrix m,
      W ∈ rowProduct S.rows ∧
      Consistent A S.answers W ∧
      1 / (200000000 * (m : ℝ) ^ 3) <
        hardObjective W (A.output S.answers : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  have hsepNorm :
      tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4) ≤ ‖w' - w‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using hsep
  obtain ⟨W, hW, hconsistent, hgap⟩ :=
    S.exists_consistent_selection_with_gap_of_pair i hw hw'
  have hnumeric := quarter_separation_gap_gt_advertised hsepNorm
  exact ⟨W, hW, hconsistent, hnumeric.trans_le hgap⟩

end ZeroOrderBounds
