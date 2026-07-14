import ZeroOrderBounds.OracleStep

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Repeated-query sanity checks

The exact Cartesian-product invariant already determines the answer when a strategy repeats an
earlier query.  This file shows that the old row bodies themselves certify that answer: every row
value is below it, one whole row body is identically equal to it, all nonconstant-row quantiles are
strictly below it, and the oracle threshold is the old answer.  Consequently there is a valid
noninformative `StepResult` which returns the old value without changing any row body.

The last conclusion is existential.  `oracleStep` is selected from the unrefined type
`StepResult S` by classical choice, so its definition does not expose which witness of that type
was chosen.  The theorem below records the geometric statement needed by the repeated-query
acceptance test without imposing a false choice-equality claim.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal

namespace ZeroOrderBounds

/-- If every product selection has the same objective value at a query, then the row bodies give
a uniform rowwise certificate for that value. -/
theorem rowsAnswerAt_of_forall_hardObjective_eq
    {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) (y : ℝ)
    (hobjective : ∀ {W : RowMatrix m}, W ∈ rowProduct rows → hardObjective W q = y) :
    RowsAnswerAt rows q y := by
  classical
  have hle : ∀ i w, w ∈ rows i → rowEvaluation q i w ≤ y := by
    intro i w hw
    obtain ⟨W₀, hW₀⟩ := rowProduct_nonempty rows
    let W : RowMatrix m := Function.update W₀ i w
    have hW : W ∈ rowProduct rows := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [W] using hw
      · simpa [W, hji] using hW₀ j
    calc
      rowEvaluation q i w = rowValue W i q := by
        have hWi : W i = w := by simp [W]
        rw [← hWi]
        exact rowEvaluation_matrix q i W
      _ ≤ hardObjective W q := rowValue_le_hardObjective W i q
      _ = y := hobjective hW
  refine ⟨hle, ?_⟩
  by_contra heqrow
  push Not at heqrow
  choose w hw hwy using heqrow
  let W : RowMatrix m := fun i ↦ w i
  have hW : W ∈ rowProduct rows := fun i ↦ hw i
  have hrowlt (i : Fin m) : rowValue W i q < y := by
    have hrowle : rowEvaluation q i (w i) ≤ y := hle i (w i) (hw i)
    have hrowne : rowEvaluation q i (w i) ≠ y := hwy i
    rw [← rowEvaluation_matrix q i W]
    exact lt_of_le_of_ne hrowle hrowne
  have hlt : hardObjective W q < y := by
    rw [hardObjective, Finset.sup'_lt_iff]
    intro i _
    exact hrowlt i
  exact (ne_of_lt hlt) (hobjective hW)

namespace RowsAnswerAt

variable {m : ℕ} [NeZero m] {rows : Fin m → RowBody m}
  {q : QuerySpace m} {y : ℝ}

/-- Every row threshold is at most a common exact product answer. -/
theorem rowThreshold_le (h : RowsAnswerAt rows q y) (i : Fin m) :
    rowThreshold rows q i ≤ y := by
  by_cases hi : RowNonconstant rows q i
  · by_contra hnot
    have hylt : y < rowThreshold rows q i := lt_of_not_ge hnot
    have hPpos :
        0 < μHE[affineDim (rows i : Set (RowSpace m))]
          (rows i : Set (RowSpace m)) := by
      rw [← intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty
        (rows i).nonempty]
      exact (rows i).volume_pos
    have hcapPos :
        0 < μHE[affineDim (rows i : Set (RowSpace m))]
          (affineCap (rows i : Set (RowSpace m)) (rowFunctional q i)
            (rowThreshold rows q i)) := by
      rw [rowThreshold_cap_measure rows q i hi]
      exact ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr (oracleAlpha_pos (m := m))).ne' hPpos.ne'
    obtain ⟨w, hwP, hwthreshold⟩ :=
      nonempty_of_euclideanHausdorffMeasure_pos hcapPos
    have hwy : rowFunctional q i w ≤ y := by
      simpa only [rowFunctional_apply] using h.1 i w hwP
    exact (not_lt_of_ge hwy) (hylt.trans_le hwthreshold)
  · let w : RowSpace m := (rows i).nonempty.some
    have hw : w ∈ rows i := (rows i).nonempty.some_mem
    have heq := rowThreshold_eq_of_not_nonconstant rows q i hi hw
    calc
      rowThreshold rows q i = rowFunctional q i w := heq.symm
      _ = rowEvaluation q i w := rowFunctional_apply q i w
      _ ≤ y := h.1 i w hw

/-- A nonconstant row's exact upper quantile is strictly below a common exact product answer. -/
theorem rowThreshold_lt (h : RowsAnswerAt rows q y) (i : Fin m)
    (hi : RowNonconstant rows q i) :
    rowThreshold rows q i < y := by
  apply lt_of_le_of_ne (h.rowThreshold_le i)
  intro hthreshold
  have hcapSub :
      affineCap (rows i : Set (RowSpace m)) (rowFunctional q i)
          (rowThreshold rows q i) ⊆
        affineSection (rows i : Set (RowSpace m)) (rowFunctional q i) y := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    have hle : rowFunctional q i w ≤ y := by
      simpa only [rowFunctional_apply] using h.1 i w hw.1
    have hge : y ≤ rowFunctional q i w := by
      rw [← hthreshold]
      exact hw.2
    exact le_antisymm hle hge
  have hcapZero :
      μHE[affineDim (rows i : Set (RowSpace m))]
          (affineCap (rows i : Set (RowSpace m)) (rowFunctional q i)
            (rowThreshold rows q i)) = 0 :=
    measure_mono_null hcapSub
      (euclideanHausdorffMeasure_affineSection_eq_zero
        (rows i).isCompact hi y)
  have hPpos :
      0 < μHE[affineDim (rows i : Set (RowSpace m))]
        (rows i : Set (RowSpace m)) := by
    rw [← intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty
      (rows i).nonempty]
    exact (rows i).volume_pos
  have hcapPos :
      0 < μHE[affineDim (rows i : Set (RowSpace m))]
        (affineCap (rows i : Set (RowSpace m)) (rowFunctional q i)
          (rowThreshold rows q i)) := by
    rw [rowThreshold_cap_measure rows q i hi]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (oracleAlpha_pos (m := m))).ne' hPpos.ne'
  exact hcapPos.ne' hcapZero

/-- Some entire row body is constant at a common exact product answer, and its threshold is that
answer. -/
theorem exists_constant_row_threshold_eq (h : RowsAnswerAt rows q y) :
    ∃ i, ¬RowNonconstant rows q i ∧ rowThreshold rows q i = y ∧
      ∀ w, w ∈ rows i → rowEvaluation q i w = y := by
  obtain ⟨i, hi⟩ := h.2
  have hconstant : ¬RowNonconstant rows q i := by
    rintro ⟨w, hw, w', hw', hne⟩
    apply hne
    calc
      rowFunctional q i w = rowEvaluation q i w := rowFunctional_apply q i w
      _ = y := hi w hw
      _ = rowEvaluation q i w' := (hi w' hw').symm
      _ = rowFunctional q i w' := (rowFunctional_apply q i w').symm
  let w : RowSpace m := (rows i).nonempty.some
  have hw : w ∈ rows i := (rows i).nonempty.some_mem
  have hthreshold := rowThreshold_eq_of_not_nonconstant rows q i hconstant hw
  have hthreshold' : rowThreshold rows q i = y := by
    calc
      rowThreshold rows q i = rowFunctional q i w := hthreshold.symm
      _ = rowEvaluation q i w := rowFunctional_apply q i w
      _ = y := hi w hw
  exact ⟨i, hconstant, hthreshold', hi⟩

/-- The oracle's maximum row threshold at a common exact product answer is exactly that answer. -/
theorem oracleThreshold_eq (h : RowsAnswerAt rows q y) :
    oracleThreshold rows q = y := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact h.rowThreshold_le i
  · obtain ⟨i, _, hi, _⟩ := h.exists_constant_row_threshold_eq
    rw [← hi]
    exact rowThreshold_le_oracleThreshold rows q i

/-- A common exact product answer cannot trigger an informative update. -/
theorem not_informative (h : RowsAnswerAt rows q y) :
    ¬Informative rows q := by
  rintro ⟨i, hi, hthreshold⟩
  have hlt := h.rowThreshold_lt i hi
  rw [h.oracleThreshold_eq] at hthreshold
  exact hlt.ne hthreshold

omit [NeZero m] in
/-- Cutting at a common exact product answer is vacuous in every row. -/
theorem affineLowerCut_eq (h : RowsAnswerAt rows q y) (i : Fin m) :
    affineLowerCut (rows i : Set (RowSpace m)) (rowFunctional q i) y = rows i := by
  ext w
  constructor
  · exact fun hw ↦ hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    change rowFunctional q i w ≤ y
    simpa only [rowFunctional_apply] using h.1 i w hw

end RowsAnswerAt

/-- A common exact answer admits a noninformative transition which returns that answer and leaves
all row bodies unchanged. -/
theorem exists_vacuousStepResult_of_rowsAnswerAt
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) {y : ℝ}
    (hanswer : RowsAnswerAt S.rows (S.nextQuery : QuerySpace m) y) :
    ∃ R : StepResult S,
      R.answer = y ∧ R.rows = S.rows ∧ R.selected = none ∧
        R.state.answers = S.answers ++ [y] ∧ R.state.rows = S.rows := by
  let R : StepResult S := {
    answer := y
    rows := S.rows
    selected := none
    subset_old := fun _ ↦ subset_rfl
    rows_answer := hanswer
    selected_nonconstant := by
      intro i hi
      simp at hi
    selected_dim := by
      intro i hi
      simp at hi
    selected_volumeReal := by
      intro i hi
      simp at hi
    unselected_dim := by
      intro i _
      rfl
    unselected_volumeReal := by
      intro i _ _
      have hα : 0 ≤ oracleAlpha m := (oracleAlpha_pos (m := m)).le
      have hV : 0 ≤ (S.rows i).volumeReal := (S.rows i).volumeReal_pos.le
      nlinarith
    constant_unchanged := by
      intro i _
      rfl }
  refine ⟨R, rfl, rfl, rfl, ?_, ?_⟩
  · rfl
  · rfl

/-- Full repeated-query sanity theorem, stated at an earlier transcript index. -/
theorem OracleState.exists_vacuousStepResult_of_repeated_query
    {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) {t : ℕ} (ht : t < S.answers.length)
    (hrepeat : S.nextQuery = A.queryAt S.answers t) :
    let y := S.answers[t]
    RowsAnswerAt S.rows (S.nextQuery : QuerySpace m) y ∧
      (∀ i, rowThreshold S.rows (S.nextQuery : QuerySpace m) i ≤ y) ∧
      (∀ i, RowNonconstant S.rows (S.nextQuery : QuerySpace m) i →
        rowThreshold S.rows (S.nextQuery : QuerySpace m) i < y) ∧
      oracleThreshold S.rows (S.nextQuery : QuerySpace m) = y ∧
      ¬Informative S.rows (S.nextQuery : QuerySpace m) ∧
      ∃ R : StepResult S,
        R.answer = y ∧ R.rows = S.rows ∧ R.selected = none ∧
          R.state.answers = S.answers ++ [y] ∧ R.state.rows = S.rows := by
  let y := S.answers[t]
  have hanswer : RowsAnswerAt S.rows (S.nextQuery : QuerySpace m) y := by
    apply rowsAnswerAt_of_forall_hardObjective_eq
    intro W hW
    have hconsistent := S.every_selection_consistent hW
    have hquery : (S.nextQuery : QuerySpace m) =
        (A.queryAt S.answers t : QuerySpace m) :=
      congrArg Subtype.val hrepeat
    rw [hquery]
    exact hconsistent t ht
  exact ⟨hanswer, hanswer.rowThreshold_le, hanswer.rowThreshold_lt,
    hanswer.oracleThreshold_eq, hanswer.not_informative,
    exists_vacuousStepResult_of_rowsAnswerAt S hanswer⟩

end ZeroOrderBounds
