import ZeroOrderBounds.VolumePotential
import ZeroOrderBounds.OracleStep
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Iterating oracle steps

This file begins with the finite bookkeeping used by the concrete resisting-
oracle iterator.  A selection log records `some i` on an informative round
which cuts row `i`, and `none` on a noninformative round.  The recursive row
counts agree exactly with the global informative-round count and control the
surviving affine dimensions.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds

/-- Predicate that a selection log marks round `t` as informative. -/
def IsInformative {m : ℕ} (selected : ℕ → Option (Fin m)) (t : ℕ) : Prop :=
  (selected t).isSome

instance {m : ℕ} (selected : ℕ → Option (Fin m)) :
    DecidablePred (IsInformative selected) :=
  fun t ↦ inferInstanceAs (Decidable (selected t).isSome)

/-- Number of times row `i` is selected during the first `T` rounds. -/
def rowSelectionCount {m : ℕ} (selected : ℕ → Option (Fin m)) :
    ℕ → Fin m → ℕ
  | 0, _ => 0
  | T + 1, i =>
      rowSelectionCount selected T i + if selected T = some i then 1 else 0

@[simp]
theorem rowSelectionCount_zero {m : ℕ} (selected : ℕ → Option (Fin m))
    (i : Fin m) :
    rowSelectionCount selected 0 i = 0 :=
  rfl

@[simp]
theorem rowSelectionCount_succ {m : ℕ} (selected : ℕ → Option (Fin m))
    (T : ℕ) (i : Fin m) :
    rowSelectionCount selected (T + 1) i =
      rowSelectionCount selected T i + if selected T = some i then 1 else 0 :=
  rfl

theorem sum_single_option_indicator {m : ℕ} [NeZero m]
    (o : Option (Fin m)) :
    ∑ i, (if o = some i then 1 else 0) = if o.isSome then 1 else 0 := by
  cases o with
  | none => simp
  | some j => simp

/-- The sum of rowwise cut counts is exactly the number of informative rounds. -/
theorem sum_rowSelectionCount {m T : ℕ} [NeZero m]
    (selected : ℕ → Option (Fin m)) :
    ∑ i, rowSelectionCount selected T i =
      informativeCount T (IsInformative selected) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [informativeCount_succ]
      simp only [rowSelectionCount_succ, Finset.sum_add_distrib]
      rw [ih, sum_single_option_indicator]
      rfl

/-- Every row is selected at most once per informative round, hence at most `T` times. -/
theorem rowSelectionCount_le {m T : ℕ} [NeZero m]
    (selected : ℕ → Option (Fin m)) (i : Fin m) :
    rowSelectionCount selected T i ≤ T := by
  calc
    rowSelectionCount selected T i ≤
        ∑ j, rowSelectionCount selected T j :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = informativeCount T (IsInformative selected) := sum_rowSelectionCount selected
    _ ≤ T := informativeCount_le T (IsInformative selected)

/-- Abstract dimension bookkeeping: initially every row has dimension `m`;
an informative selection of `i` lowers exactly that row by one, and such a
selection can occur only while its dimension is positive. -/
theorem dimension_eq_sub_rowSelectionCount
    {m T : ℕ} [NeZero m]
    (selected : ℕ → Option (Fin m)) (dim : ℕ → Fin m → ℕ)
    (hinit : ∀ i, dim 0 i = m)
    (hstep : ∀ t i,
      dim (t + 1) i =
        if selected t = some i then dim t i - 1 else dim t i)
    (hpositive : ∀ t i, selected t = some i → 0 < dim t i) :
    ∀ i, dim T i = m - rowSelectionCount selected T i := by
  induction T with
  | zero =>
      intro i
      simp [hinit]
  | succ T ih =>
      intro i
      rw [hstep, rowSelectionCount_succ]
      by_cases hi : selected T = some i
      · rw [if_pos hi, if_pos hi, ih i]
        have hp := hpositive T i hi
        have hcountLt : rowSelectionCount selected T i < m := by
          rw [ih i] at hp
          omega
        omega
      · rw [if_neg hi, if_neg hi, ih i]
        omega

/-! ## One-step product-volume estimates -/

namespace StepResult

variable {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
  {S : OracleState A}

/-- Every unselected row satisfies the uniform retention bound; constant rows
are unchanged and `retention ≤ 1`. -/
theorem unselected_volumeReal_uniform (R : StepResult S) (i : Fin m)
    (hi : R.selected ≠ some i) :
    retention m * (S.rows i).volumeReal ≤ (R.rows i).volumeReal := by
  by_cases hnonconstant : RowNonconstant S.rows (S.nextQuery : QuerySpace m) i
  · simpa [retention, oracleAlpha] using
      R.unselected_volumeReal i hi hnonconstant
  · rw [R.constant_unchanged i hnonconstant]
    calc
      retention m * (S.rows i).volumeReal ≤
          1 * (S.rows i).volumeReal :=
        mul_le_mul_of_nonneg_right (retention_le_one m)
          (S.rows i).volumeReal_pos.le
      _ = (S.rows i).volumeReal := one_mul _

/-- A noninformative step retains at least `retention^m` of the product. -/
theorem product_volume_noninformative (R : StepResult S)
    (hR : R.selected = none) :
    retention m ^ m * ∏ i, (S.rows i).volumeReal ≤
      ∏ i, (R.rows i).volumeReal := by
  have hprod :
      ∏ i, retention m * (S.rows i).volumeReal ≤
        ∏ i, (R.rows i).volumeReal := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (retention_nonneg (Nat.pos_of_ne_zero (NeZero.ne m)))
        (S.rows i).volumeReal_pos.le
    · intro i _
      apply R.unselected_volumeReal_uniform i
      simp [hR]
  calc
    retention m ^ m * ∏ i, (S.rows i).volumeReal =
        ∏ i, retention m * (S.rows i).volumeReal := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i, (R.rows i).volumeReal := hprod

/-- An informative step pays the slicing factor on its selected row and the
retention factor on every other row. -/
theorem product_volume_informative (R : StepResult S) {j : Fin m}
    (hR : R.selected = some j) :
    (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) *
        ∏ i, (S.rows i).volumeReal ≤
      ∏ i, (R.rows i).volumeReal := by
  let factor : Fin m → ℝ := fun i ↦
    if i = j then 1 / (8 * (m : ℝ) * tau m) else retention m
  have hfactor_nonneg : ∀ i, 0 ≤ factor i := by
    intro i
    dsimp [factor]
    split_ifs
    · positivity [tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))]
    · exact retention_nonneg (Nat.pos_of_ne_zero (NeZero.ne m))
  have hrow : ∀ i, factor i * (S.rows i).volumeReal ≤ (R.rows i).volumeReal := by
    intro i
    by_cases hij : i = j
    · subst i
      calc
        factor j * (S.rows j).volumeReal =
            (S.rows j).volumeReal / (8 * (m : ℝ) * tau m) := by
          simp [factor]
          ring
        _ ≤ (R.rows j).volumeReal := R.selected_volumeReal hR
    · have hi : R.selected ≠ some i := by
        intro hRi
        have hji : j = i := Option.some.inj (hR.symm.trans hRi)
        exact hij hji.symm
      simpa [factor, hij] using R.unselected_volumeReal_uniform i hi
  have hprod :
      ∏ i, factor i * (S.rows i).volumeReal ≤
        ∏ i, (R.rows i).volumeReal := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (hfactor_nonneg i) (S.rows i).volumeReal_pos.le
    · intro i _
      exact hrow i
  have hfactor_prod :
      ∏ i, factor i =
        (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) := by
    have hrest :
        ∏ i ∈ (Finset.univ : Finset (Fin m)).erase j, factor i =
          retention m ^ (m - 1) := by
      calc
        ∏ i ∈ (Finset.univ : Finset (Fin m)).erase j, factor i =
            ∏ _i ∈ (Finset.univ : Finset (Fin m)).erase j, retention m := by
          apply Finset.prod_congr rfl
          intro i hi
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          simp [factor, hij]
        _ = retention m ^ (m - 1) := by simp
    calc
      ∏ i, factor i = factor j *
          ∏ i ∈ (Finset.univ : Finset (Fin m)).erase j, factor i := by
        rw [mul_comm, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      _ = (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) := by
        rw [hrest]
        simp [factor]
  calc
    (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) *
          ∏ i, (S.rows i).volumeReal =
        (∏ i, factor i) * ∏ i, (S.rows i).volumeReal := by rw [hfactor_prod]
    _ = ∏ i, factor i * (S.rows i).volumeReal := Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, (R.rows i).volumeReal := hprod

/-- Unified conditional form expected by `volumePotential_of_oracle_steps`. -/
theorem product_volume_step (R : StepResult S) :
    if R.selected.isSome then
      (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) *
          (∏ i, (S.rows i).volumeReal) ≤ ∏ i, (R.rows i).volumeReal
    else
      retention m ^ m * (∏ i, (S.rows i).volumeReal) ≤
        ∏ i, (R.rows i).volumeReal := by
  cases hsel : R.selected with
  | none => simpa [hsel] using R.product_volume_noninformative hsel
  | some j => simpa [hsel] using R.product_volume_informative hsel

end StepResult

/-! ## Concrete oracle trajectory -/

/-- State reached after exactly `t` oracle transitions. -/
def oracleStateAt {m : ℕ} [NeZero m] (A : DeterministicStrategy m) :
    ℕ → OracleState A
  | 0 => OracleState.initial A
  | t + 1 => oracleNextState (oracleStateAt A t)

@[simp]
theorem oracleStateAt_zero {m : ℕ} [NeZero m] (A : DeterministicStrategy m) :
    oracleStateAt A 0 = OracleState.initial A :=
  rfl

@[simp]
theorem oracleStateAt_succ {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (t : ℕ) :
    oracleStateAt A (t + 1) = oracleNextState (oracleStateAt A t) :=
  rfl

/-- Transition certificate used at round `t`. -/
def oracleStepAt {m : ℕ} [NeZero m] (A : DeterministicStrategy m) (t : ℕ) :
    StepResult (oracleStateAt A t) :=
  oracleStep (oracleStateAt A t)

/-- Selected row at round `t`, or `none` for a noninformative round. -/
def oracleSelected {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (t : ℕ) : Option (Fin m) :=
  (oracleStepAt A t).selected

/-- Number of selections of row `i` during the first `T` rounds of the
concrete trajectory. -/
def oracleRowCount {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (T : ℕ) (i : Fin m) : ℕ :=
  rowSelectionCount (oracleSelected A) T i

/-- Product of all row volumes after `t` transitions. -/
def oracleTotalVolume {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (t : ℕ) : ℝ :=
  ∏ i, ((oracleStateAt A t).rows i).volumeReal

@[simp]
theorem oracleStateAt_round {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    (oracleStateAt A t).round = t := by
  induction t with
  | zero => simp [oracleStateAt]
  | succ t ih =>
      rw [oracleStateAt_succ, oracleNextState_round, ih]

@[simp]
theorem oracleStateAt_answers_length {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    (oracleStateAt A t).answers.length = t := by
  simpa [OracleState.round] using oracleStateAt_round A t

@[simp]
theorem oracleStateAt_succ_rows {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    (oracleStateAt A (t + 1)).rows = (oracleStepAt A t).rows :=
  rfl

@[simp]
theorem oracleStateAt_succ_answers {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    (oracleStateAt A (t + 1)).answers =
      (oracleStateAt A t).answers ++ [(oracleStepAt A t).answer] :=
  rfl

theorem oracleStateAt_product_consistent {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    ProductConsistent A (oracleStateAt A t).answers (oracleStateAt A t).rows :=
  (oracleStateAt A t).product_consistent

/-! ## Concrete dimension and selection-count identities -/

theorem oracle_dim_step {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) (i : Fin m) :
    ((oracleStateAt A (t + 1)).rows i).dim =
      if oracleSelected A t = some i then
        ((oracleStateAt A t).rows i).dim - 1
      else ((oracleStateAt A t).rows i).dim := by
  let R := oracleStepAt A t
  change (R.rows i).dim =
    if R.selected = some i then ((oracleStateAt A t).rows i).dim - 1
    else ((oracleStateAt A t).rows i).dim
  cases hsel : R.selected with
  | none =>
      have hne : R.selected ≠ some i := by rw [hsel]; simp
      simpa using R.unselected_dim i hne
  | some j =>
      by_cases hij : j = i
      · subst j
        simpa using R.selected_dim hsel
      · have hne : some j ≠ some i := by
          intro h
          exact hij (Option.some.inj h)
        have hne' : R.selected ≠ some i := by simpa only [hsel] using hne
        simpa [hij] using R.unselected_dim i hne'

theorem oracle_selected_dim_pos {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) (i : Fin m)
    (hsel : oracleSelected A t = some i) :
    0 < ((oracleStateAt A t).rows i).dim := by
  have hnon := (oracleStepAt A t).selected_nonconstant hsel
  have hne := affineDim_ne_zero_of_nonconstantOn
    ((oracleStateAt A t).rows i) hnon
  exact Nat.pos_of_ne_zero hne

/-- Surviving dimension is initial dimension minus the exact number of times
the row was selected. -/
theorem oracleStateAt_dim_eq {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (T : ℕ) (i : Fin m) :
    ((oracleStateAt A T).rows i).dim = m - oracleRowCount A T i := by
  apply dimension_eq_sub_rowSelectionCount
    (selected := oracleSelected A)
    (dim := fun t i ↦ ((oracleStateAt A t).rows i).dim)
    (T := T)
  · intro j
    exact initialRowBody.dim_eq (Nat.pos_of_ne_zero (NeZero.ne m))
  · exact oracle_dim_step A
  · exact oracle_selected_dim_pos A

/-- A row cannot be selected more than `m` times. -/
theorem oracleRowCount_le_m {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (T : ℕ) (i : Fin m) :
    oracleRowCount A T i ≤ m := by
  induction T with
  | zero => simp [oracleRowCount]
  | succ T ih =>
      rw [oracleRowCount, rowSelectionCount_succ]
      by_cases hsel : oracleSelected A T = some i
      · rw [if_pos hsel]
        have hpos := oracle_selected_dim_pos A T i hsel
        rw [oracleStateAt_dim_eq A T i] at hpos
        change 0 < m - rowSelectionCount (oracleSelected A) T i at hpos
        change rowSelectionCount (oracleSelected A) T i + 1 ≤ m
        omega
      · rw [if_neg hsel]
        exact ih

theorem sum_oracleRowCount {m T : ℕ} [NeZero m]
    (A : DeterministicStrategy m) :
    ∑ i, oracleRowCount A T i =
      informativeCount T (IsInformative (oracleSelected A)) := by
  exact sum_rowSelectionCount (oracleSelected A)

theorem sum_oracleRowCount_le {m T : ℕ} [NeZero m]
    (A : DeterministicStrategy m) :
    ∑ i, oracleRowCount A T i ≤ T := by
  rw [sum_oracleRowCount]
  exact informativeCount_le T (IsInformative (oracleSelected A))

/-! ## Product-volume trajectory and final budgets -/

theorem oracleTotalVolume_nonneg {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    0 ≤ oracleTotalVolume A t := by
  apply Finset.prod_nonneg
  intro i _
  exact ((oracleStateAt A t).rows i).volumeReal_pos.le

theorem oracleTotalVolume_zero {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) :
    oracleTotalVolume A 0 =
      ∏ _i : Fin m, (initialRowBody m).volumeReal :=
  rfl

theorem oracleTotalVolume_step {m : ℕ} [NeZero m]
    (A : DeterministicStrategy m) (t : ℕ) :
    if IsInformative (oracleSelected A) t then
      (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) *
          oracleTotalVolume A t ≤ oracleTotalVolume A (t + 1)
    else
      retention m ^ m * oracleTotalVolume A t ≤
        oracleTotalVolume A (t + 1) := by
  simpa only [IsInformative, oracleSelected, oracleStepAt,
    oracleTotalVolume, oracleStateAt_succ_rows] using
      (oracleStepAt A t).product_volume_step

/-- The full normalized-product and entropy conclusion for the concrete
`T`-round oracle run. -/
theorem oracleRun_volumePotential {m T : ℕ} [NeZero m]
    (A : DeterministicStrategy m) :
    ((3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^
          informativeCount T (IsInformative (oracleSelected A)) ≤
        ∏ i, ((oracleStateAt A T).rows i).normalizedVolume) ∧
      (∑ i, rowEntropy (((oracleStateAt A T).rows i).normalizedVolume) ≤
        (T : ℝ) * entropyScale m) := by
  apply volumePotential_of_oracle_steps
    (hm := Nat.pos_of_ne_zero (NeZero.ne m))
    (totalVolume := oracleTotalVolume A)
    (informative := IsInformative (oracleSelected A))
    (rows := (oracleStateAt A T).rows)
    (c := oracleRowCount A T)
  · exact oracleTotalVolume_nonneg A
  · exact oracleTotalVolume_zero A
  · exact oracleTotalVolume_step A
  · rfl
  · exact oracleRowCount_le_m A T
  · exact oracleStateAt_dim_eq A T
  · exact sum_oracleRowCount A

/-- Final-state hypotheses in exactly the round-budget form consumed by
`Main.exists_advertised_gap_of_round_budgets`. -/
theorem oracleRun_final_budgets {m T : ℕ} [NeZero m]
    (A : DeterministicStrategy m) :
    (∀ i, ((oracleStateAt A T).rows i).dim = m - oracleRowCount A T i) ∧
      (∑ i, oracleRowCount A T i ≤ T) ∧
      (∑ i, rowEntropy (((oracleStateAt A T).rows i).normalizedVolume) ≤
        (T : ℝ) * entropyScale m) := by
  refine ⟨oracleStateAt_dim_eq A T, sum_oracleRowCount_le A, ?_⟩
  exact (oracleRun_volumePotential A).2

end ZeroOrderBounds
