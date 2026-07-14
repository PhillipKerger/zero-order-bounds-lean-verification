import ZeroOrderBounds.ProjectionGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds

/-- The coordinate vector used to describe tangent directions of the simplex. -/
def weightBasis {m : ℕ} (i : Fin m) : Fin m → ℝ :=
  fun k ↦ if k = i then 1 else 0

/-- The simplex tangent which moves mass from coordinate `j` to coordinate `i`. -/
def simplexTangent {m : ℕ} (i j : Fin m) : Fin m → ℝ :=
  weightBasis i - weightBasis j

@[simp]
theorem weightBasis_apply {m : ℕ} (i k : Fin m) :
    weightBasis i k = if k = i then 1 else 0 :=
  rfl

/-- The barycentric image of a simplex tangent is the corresponding slope
difference. -/
theorem barycentricMap_simplexTangent {m : ℕ} (W : RowMatrix m)
    (i j : Fin m) :
    barycentricMap W (simplexTangent i j) = slope W i - slope W j := by
  rw [barycentricMap_apply]
  simp only [simplexTangent, weightBasis, Pi.sub_apply]
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib]
  simp

/-- The squared norm of a barycentric combination. -/
def barycentricEnergy {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ) : ℝ :=
  ‖barycentricMap W w‖ ^ 2

/-- The stationarity coordinate at arbitrary weights. -/
def stationarityAt {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  inner ℝ (barycentricMap W w) (slope W i)

/-- The row-space block of a barycentric combination. -/
def weightedRow {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ) : RowSpace m :=
  ∑ i, w i • W i

@[simp]
theorem secondBlock_barycentricMap {m : ℕ} (W : RowMatrix m)
    (w : Fin m → ℝ) :
    secondBlock (barycentricMap W w) = weightedRow W w := by
  rw [barycentricMap_eq_joinBlocks]
  rfl

/-- Coordinate formula for the stationarity quantities `g_i`. -/
theorem stationarityAt_eq {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ)
    (i : Fin m) :
    stationarityAt W w i =
      a ^ 2 * w i + inner ℝ (W i) (weightedRow W w) := by
  rw [stationarityAt, real_inner_comm, inner_slope,
    firstBlock_barycentricMap_apply, secondBlock_barycentricMap]
  ring

/-- The curvature in the exact tangent expansion. -/
def tangentCurvature {m : ℕ} (W : RowMatrix m) (i j : Fin m) : ℝ :=
  ‖slope W i - slope W j‖ ^ 2

/-- The curvature is the sum of the first-block and row-block energies. -/
theorem tangentCurvature_eq {m : ℕ} (W : RowMatrix m) (i j : Fin m) :
    tangentCurvature W i j =
      a ^ 2 * ‖weightVector (simplexTangent i j)‖ ^ 2 + ‖W i - W j‖ ^ 2 := by
  have hrow : ∑ k, simplexTangent i j k • W k = W i - W j := by
    simp only [simplexTangent, weightBasis, Pi.sub_apply]
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    simp
  rw [tangentCurvature, ← barycentricMap_simplexTangent W i j,
    barycentricMap_eq_joinBlocks, joinBlocks_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos a_pos, mul_pow, hrow]

/-- Tangent curvature is strictly positive for two distinct coordinates. -/
theorem tangentCurvature_pos {m : ℕ} (W : RowMatrix m) {i j : Fin m}
    (hij : i ≠ j) :
    0 < tangentCurvature W i j := by
  have hslope : slope W i ≠ slope W j := by
    intro h
    have hcoord := congrArg (fun q : QuerySpace m ↦ firstBlock q i) h
    simp [hij, a] at hcoord
  exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hslope))

/-- Exact quadratic expansion along a simplex tangent, equation (8.1). -/
theorem barycentricEnergy_add_tangent {m : ℕ} (W : RowMatrix m)
    (w : Fin m → ℝ) (i j : Fin m) (t : ℝ) :
    barycentricEnergy W (w + t • simplexTangent i j) - barycentricEnergy W w =
      2 * t * (stationarityAt W w i - stationarityAt W w j) +
        t ^ 2 * ‖slope W i - slope W j‖ ^ 2 := by
  have himage : barycentricMap W (w + t • simplexTangent i j) =
      barycentricMap W w + t • (slope W i - slope W j) := by
    rw [map_add, map_smul, barycentricMap_simplexTangent]
  rw [barycentricEnergy, barycentricEnergy, himage, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_right,
    stationarityAt, inner_sub_right]
  rw [mul_pow, sq_abs]
  ring

/-- Equation (8.1), with the curvature named explicitly. -/
theorem barycentricEnergy_add_tangent_eq {m : ℕ} (W : RowMatrix m)
    (w : Fin m → ℝ) (i j : Fin m) (t : ℝ) :
    barycentricEnergy W (w + t • simplexTangent i j) - barycentricEnergy W w =
      2 * t * (stationarityAt W w i - stationarityAt W w j) +
        t ^ 2 * tangentCurvature W i j := by
  simpa [tangentCurvature] using barycentricEnergy_add_tangent W w i j t

/-- The second block of the selected minimum-norm barycentric point. -/
def zBlock {m : ℕ} [NeZero m] (W : RowMatrix m) : RowSpace m :=
  secondBlock (minPoint W)

@[simp]
theorem zBlock_eq_weightedRow {m : ℕ} [NeZero m] (W : RowMatrix m) :
    zBlock W = weightedRow W (minWeights W) := by
  rw [zBlock, minPoint, barycentricMap_eq_joinBlocks]
  rfl

/-- The selected stationarity coordinates. -/
def stationarityValue {m : ℕ} [NeZero m] (W : RowMatrix m) (i : Fin m) : ℝ :=
  stationarityAt W (minWeights W) i

/-- Explicit formula for a selected stationarity coordinate. -/
theorem stationarityValue_eq {m : ℕ} [NeZero m] (W : RowMatrix m)
    (i : Fin m) :
    stationarityValue W i =
      a ^ 2 * (minWeights W : Fin m → ℝ) i + inner ℝ (W i) (zBlock W) := by
  rw [stationarityValue, stationarityAt_eq, zBlock_eq_weightedRow]

/-- The row block is a convex combination of admissible rows and therefore
stays in the row uncertainty ball. -/
theorem norm_zBlock_le_tau {m : ℕ} [NeZero m] (W : RowMatrix m)
    (hW : Admissible W) :
    ‖zBlock W‖ ≤ tau m := by
  rw [zBlock_eq_weightedRow, weightedRow]
  calc
    ‖∑ i, (minWeights W : Fin m → ℝ) i • W i‖ ≤
        ∑ i, ‖(minWeights W : Fin m → ℝ) i • W i‖ :=
      norm_sum_le _ _
    _ = ∑ i, (minWeights W : Fin m → ℝ) i * ‖W i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : 0 ≤ (minWeights W : Fin m → ℝ) i :=
        (minWeights W).property.1 i
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi]
    _ ≤ ∑ i, (minWeights W : Fin m → ℝ) i * tau m := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hW i) ((minWeights W).property.1 i)
    _ = tau m := by
      have hsum : ∑ i, (minWeights W : Fin m → ℝ) i = 1 :=
        (minWeights W).property.2
      rw [← Finset.sum_mul, hsum, one_mul]

/-- Projection against a simplex vertex bounds every stationarity coordinate
from below by the squared norm of the minimum point. -/
theorem norm_minPoint_sq_le_stationarityValue {m : ℕ} [NeZero m]
    (W : RowMatrix m) (i : Fin m) :
    ‖minPoint W‖ ^ 2 ≤ stationarityValue W i := by
  simpa [stationarityValue, stationarityAt, minPoint] using
    norm_minPoint_sq_le_inner_slope W i

/-- Averaging stationarity coordinates with the minimizing weights recovers
the squared norm of the minimum point. -/
theorem sum_minWeights_mul_stationarityValue {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    ∑ i, (minWeights W : Fin m → ℝ) i * stationarityValue W i =
      ‖minPoint W‖ ^ 2 := by
  calc
    ∑ i, (minWeights W : Fin m → ℝ) i * stationarityValue W i =
        ∑ i, inner ℝ (minPoint W)
          ((minWeights W : Fin m → ℝ) i • slope W i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [stationarityValue, stationarityAt, minPoint,
        real_inner_smul_right]
    _ = inner ℝ (minPoint W)
        (∑ i, (minWeights W : Fin m → ℝ) i • slope W i) := by
      rw [inner_sum]
    _ = inner ℝ (minPoint W) (minPoint W) := by
      rw [← barycentricMap_apply]
      rfl
    _ = ‖minPoint W‖ ^ 2 := real_inner_self_eq_norm_sq (minPoint W)

/-- Every coordinate carrying positive minimizing mass satisfies exact
stationarity. -/
theorem stationarityValue_eq_norm_sq_of_pos {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m)
    (hj : 0 < (minWeights W : Fin m → ℝ) j) :
    stationarityValue W j = ‖minPoint W‖ ^ 2 := by
  let gap : Fin m → ℝ := fun i ↦
    (minWeights W : Fin m → ℝ) i *
      (stationarityValue W i - ‖minPoint W‖ ^ 2)
  have hgap_nonneg : ∀ i, 0 ≤ gap i := by
    intro i
    exact mul_nonneg ((minWeights W).property.1 i)
      (sub_nonneg.mpr (norm_minPoint_sq_le_stationarityValue W i))
  have hgap_sum : ∑ i, gap i = 0 := by
    simp only [gap, mul_sub]
    rw [Finset.sum_sub_distrib, sum_minWeights_mul_stationarityValue]
    have hsum : ∑ i, (minWeights W : Fin m → ℝ) i = 1 :=
      (minWeights W).property.2
    rw [← Finset.sum_mul, hsum, one_mul, sub_self]
  have hjle : gap j ≤ ∑ i, gap i :=
    Finset.single_le_sum (fun i _ ↦ hgap_nonneg i) (Finset.mem_univ j)
  rw [hgap_sum] at hjle
  have hdiff : stationarityValue W j - ‖minPoint W‖ ^ 2 ≤ 0 := by
    by_contra hnot
    have hdiffpos : 0 < stationarityValue W j - ‖minPoint W‖ ^ 2 :=
      lt_of_not_ge hnot
    have hgap_pos : 0 < gap j := mul_pos hj hdiffpos
    linarith
  exact le_antisymm (sub_nonpos.mp hdiff)
    (norm_minPoint_sq_le_stationarityValue W j)

/-- Some simplex coordinate is at least the uniform weight. -/
theorem exists_inv_nat_le_minWeight {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    ∃ j : Fin m, (m : ℝ)⁻¹ ≤ (minWeights W : Fin m → ℝ) j := by
  have hsum : ∑ i, (minWeights W : Fin m → ℝ) i = 1 :=
    (minWeights W).property.2
  have hconst : ∑ _i : Fin m, (m : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ]
    rw [smul_eq_mul, mul_inv_cancel₀ natCast_m_ne_zero]
  by_contra h
  push Not at h
  have hlt :
      (∑ i, (minWeights W : Fin m → ℝ) i) <
        ∑ _i : Fin m, (m : ℝ)⁻¹ := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    exact h i
  rw [hsum, hconst] at hlt
  exact (lt_irrefl 1) hlt

/-- The scale choice `Gamma = 100` makes the row perturbation energy much
smaller than the first-block uniform energy. -/
theorem two_tau_sq_lt_a_sq_div_nat {m : ℕ} [NeZero m] :
    2 * tau m ^ 2 < a ^ 2 / (m : ℝ) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  rw [tau, Gamma, a]
  field_simp
  nlinarith

/-- If a minimizing coordinate vanished, its stationarity value would be at
most the row energy `tau^2`. -/
theorem stationarityValue_le_tau_sq_of_eq_zero {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m)
    (hi : (minWeights W : Fin m → ℝ) i = 0) :
    stationarityValue W i ≤ tau m ^ 2 := by
  have hz := norm_zBlock_le_tau W hW
  rw [stationarityValue_eq, hi, mul_zero, zero_add]
  calc
    inner ℝ (W i) (zBlock W) ≤ |inner ℝ (W i) (zBlock W)| :=
      le_abs_self _
    _ ≤ ‖W i‖ * ‖zBlock W‖ := abs_real_inner_le_norm _ _
    _ ≤ tau m * tau m := by
      exact mul_le_mul (hW i) hz (norm_nonneg _) (tau_pos (Nat.pos_of_ne_zero
        (NeZero.ne m))).le
    _ = tau m ^ 2 := by ring

/-- A coordinate of at least uniform mass has stationarity value at least the
uniform first-block energy minus `tau^2`. -/
theorem a_sq_div_nat_sub_tau_sq_le_stationarityValue {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (j : Fin m)
    (hj : (m : ℝ)⁻¹ ≤ (minWeights W : Fin m → ℝ) j) :
    a ^ 2 / (m : ℝ) - tau m ^ 2 ≤ stationarityValue W j := by
  have hz := norm_zBlock_le_tau W hW
  have habs : |inner ℝ (W j) (zBlock W)| ≤ tau m ^ 2 := by
    calc
      |inner ℝ (W j) (zBlock W)| ≤ ‖W j‖ * ‖zBlock W‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ tau m * tau m := by
        exact mul_le_mul (hW j) hz (norm_nonneg _) (tau_pos
          (Nat.pos_of_ne_zero (NeZero.ne m))).le
      _ = tau m ^ 2 := by ring
  have hinner : -tau m ^ 2 ≤ inner ℝ (W j) (zBlock W) :=
    neg_le_of_abs_le habs
  rw [stationarityValue_eq]
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hfirst : a ^ 2 / (m : ℝ) ≤
      a ^ 2 * (minWeights W : Fin m → ℝ) j := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hj ha2
  linarith

/-- Every minimizing barycentric coordinate is strictly positive. -/
theorem minWeights_pos {m : ℕ} [NeZero m] (W : RowMatrix m)
    (hW : Admissible W) (i : Fin m) :
    0 < (minWeights W : Fin m → ℝ) i := by
  have hi_nonneg := (minWeights W).property.1 i
  by_contra hi_not
  have hi : (minWeights W : Fin m → ℝ) i = 0 :=
    le_antisymm (le_of_not_gt hi_not) hi_nonneg
  obtain ⟨j, hj⟩ := exists_inv_nat_le_minWeight W
  have hinv_pos : 0 < (m : ℝ)⁻¹ := inv_pos.mpr natCast_m_pos
  have hjpos : 0 < (minWeights W : Fin m → ℝ) j :=
    hinv_pos.trans_le hj
  have hstation_j := stationarityValue_eq_norm_sq_of_pos W j hjpos
  have hji : stationarityValue W j ≤ stationarityValue W i := by
    rw [hstation_j]
    exact norm_minPoint_sq_le_stationarityValue W i
  have hiupper := stationarityValue_le_tau_sq_of_eq_zero W hW i hi
  have hjlower := a_sq_div_nat_sub_tau_sq_le_stationarityValue W hW j hj
  have hscale : 2 * tau m ^ 2 < a ^ 2 / (m : ℝ) :=
    two_tau_sq_lt_a_sq_div_nat
  linarith

/-- All selected stationarity coordinates equal the squared minimum norm. -/
theorem stationarityValue_eq_norm_sq {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    stationarityValue W i = ‖minPoint W‖ ^ 2 :=
  stationarityValue_eq_norm_sq_of_pos W i (minWeights_pos W hW i)

/-- Pairwise equality of the stationarity coordinates, equation (8.2). -/
theorem stationarityValue_eq_stationarityValue {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i j : Fin m) :
    stationarityValue W i = stationarityValue W j := by
  rw [stationarityValue_eq_norm_sq W hW i,
    stationarityValue_eq_norm_sq W hW j]

/-- The unweighted sum of stationarity coordinates in terms of the mean and
the selected row block. -/
theorem sum_stationarityValue_eq {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    ∑ i, stationarityValue W i =
      a ^ 2 + (m : ℝ) * inner ℝ (rowMean W) (zBlock W) := by
  calc
    ∑ i, stationarityValue W i =
        ∑ i, (a ^ 2 * (minWeights W : Fin m → ℝ) i +
          inner ℝ (W i) (zBlock W)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact stationarityValue_eq W i
    _ = a ^ 2 * ∑ i, (minWeights W : Fin m → ℝ) i +
        inner ℝ (∑ i, W i) (zBlock W) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_inner]
    _ = a ^ 2 + (m : ℝ) * inner ℝ (rowMean W) (zBlock W) := by
      have hweights : ∑ i, (minWeights W : Fin m → ℝ) i = 1 :=
        (minWeights W).property.2
      rw [hweights, mul_one,
        ← natCast_smul_rowMean W, real_inner_smul_left]

/-- Averaging equation (8.2) identifies its common scalar. -/
theorem norm_minPoint_sq_eq_mean_formula {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ^ 2 =
      a ^ 2 / (m : ℝ) + inner ℝ (rowMean W) (zBlock W) := by
  have hall : ∑ i, stationarityValue W i =
      ∑ _i : Fin m, ‖minPoint W‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact stationarityValue_eq_norm_sq W hW i
  have hsum := sum_stationarityValue_eq W
  rw [hall] at hsum
  simp only [Finset.sum_const, Finset.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul] at hsum
  have hm0 : (m : ℝ) ≠ 0 := natCast_m_ne_zero
  field_simp [hm0]
  field_simp [hm0] at hsum
  linarith

/-- Explicit formula for every minimizing weight, equation (8.3). -/
theorem minWeights_apply_eq {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    (minWeights W : Fin m → ℝ) i =
      (m : ℝ)⁻¹ +
        inner ℝ (rowMean W - W i) (zBlock W) / a ^ 2 := by
  have hstation := stationarityValue_eq_norm_sq W hW i
  rw [stationarityValue_eq, norm_minPoint_sq_eq_mean_formula W hW] at hstation
  rw [inner_sub_left]
  have ha0 : a ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt a_pos)
  have hm0 : (m : ℝ) ≠ 0 := natCast_m_ne_zero
  have hdiff :
      (minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹ =
        (inner ℝ (rowMean W) (zBlock W) -
          inner ℝ (W i) (zBlock W)) / a ^ 2 := by
    apply (eq_div_iff ha0).2
    field_simp [hm0] at hstation ⊢
    nlinarith
  linarith

/-- Block decomposition of the minimum-norm barycentric point. -/
theorem minPoint_eq_joinBlocks_weights_zBlock {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    minPoint W =
      joinBlocks (a • weightVector (minWeights W)) (zBlock W) := by
  rw [minPoint, barycentricMap_eq_joinBlocks, zBlock_eq_weightedRow]
  rfl

/-- The optimizer's second block is the normalized negative of `zBlock`. -/
theorem secondBlock_hardOptimizer {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    secondBlock (hardOptimizer W) =
      (-(‖minPoint W‖)⁻¹) • zBlock W := by
  ext i
  rfl

/-- Multiplying covariance by the number of rows removes its averaging
factor and, because centered rows sum to zero, permits replacing the final
centered row by the original row. -/
theorem natCast_smul_covariance_eq_sum_inner_smul_row {m : ℕ} [NeZero m]
    (W : RowMatrix m) (u : RowSpace m) :
    (m : ℝ) • covariance W u =
      ∑ i, inner ℝ (centeredRow W i) u • W i := by
  have hcoeff : ∑ i, inner ℝ (centeredRow W i) u = 0 := by
    rw [← sum_inner, sum_centeredRow]
    simp
  rw [covariance_apply, smul_smul,
    mul_inv_cancel₀ natCast_m_ne_zero, one_smul]
  calc
    ∑ i, inner ℝ (centeredRow W i) u • centeredRow W i =
        ∑ i, (inner ℝ (centeredRow W i) u • W i -
          inner ℝ (centeredRow W i) u • rowMean W) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [centeredRow, smul_sub]
    _ = (∑ i, inner ℝ (centeredRow W i) u • W i) -
        ∑ i, inner ℝ (centeredRow W i) u • rowMean W := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, inner ℝ (centeredRow W i) u • W i) -
        (∑ i, inner ℝ (centeredRow W i) u) • rowMean W := by
      rw [Finset.sum_smul]
    _ = ∑ i, inner ℝ (centeredRow W i) u • W i := by
      rw [hcoeff, zero_smul, sub_zero]

/-- The correction term in the explicit weight formula is precisely the
negative scaled covariance. -/
theorem sum_weight_correction_eq_neg_covariance {m : ℕ} [NeZero m]
    (W : RowMatrix m) (u : RowSpace m) :
    ∑ i, (inner ℝ (rowMean W - W i) u / a ^ 2) • W i =
      (-(m : ℝ) / a ^ 2) • covariance W u := by
  have ha0 : a ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt a_pos)
  calc
    ∑ i, (inner ℝ (rowMean W - W i) u / a ^ 2) • W i =
        ∑ i, ((-(a ^ 2)⁻¹) * inner ℝ (centeredRow W i) u) • W i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [centeredRow, inner_sub_left, inner_sub_left]
      field_simp [ha0]
      ring
    _ = (-(a ^ 2)⁻¹) •
        (∑ i, inner ℝ (centeredRow W i) u • W i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
    _ = (-(a ^ 2)⁻¹) • ((m : ℝ) • covariance W u) := by
      rw [natCast_smul_covariance_eq_sum_inner_smul_row]
    _ = (-(m : ℝ) / a ^ 2) • covariance W u := by
      rw [smul_smul]
      congr 1
      field_simp [ha0]

/-- Substitution of the explicit minimizing weights gives the covariance
fixed-point equation in subtraction form. -/
theorem zBlock_eq_mean_sub_covariance {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    zBlock W = rowMean W - ((m : ℝ) / a ^ 2) • covariance W (zBlock W) := by
  have hmean : ∑ i, ((m : ℝ)⁻¹) • W i = rowMean W := by
    rw [← Finset.smul_sum]
    rfl
  calc
    zBlock W = ∑ i, (minWeights W : Fin m → ℝ) i • W i := by
      rw [zBlock_eq_weightedRow]
      rfl
    _ = ∑ i, ((m : ℝ)⁻¹ +
        inner ℝ (rowMean W - W i) (zBlock W) / a ^ 2) • W i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [minWeights_apply_eq W hW i]
    _ = ∑ i, (((m : ℝ)⁻¹) • W i +
        (inner ℝ (rowMean W - W i) (zBlock W) / a ^ 2) • W i) := by
      simp_rw [add_smul]
    _ = (∑ i, ((m : ℝ)⁻¹) • W i) +
        ∑ i, (inner ℝ (rowMean W - W i) (zBlock W) / a ^ 2) • W i := by
      rw [Finset.sum_add_distrib]
    _ = rowMean W + (-(m : ℝ) / a ^ 2) • covariance W (zBlock W) := by
      rw [hmean, sum_weight_correction_eq_neg_covariance]
    _ = rowMean W - ((m : ℝ) / a ^ 2) • covariance W (zBlock W) := by
      rw [show (-(m : ℝ) / a ^ 2) = -((m : ℝ) / a ^ 2) by ring,
        neg_smul, sub_eq_add_neg]

/-- Additive form of the covariance equation. -/
theorem zBlock_add_covariance_eq_mean {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    zBlock W + ((m : ℝ) / a ^ 2) • covariance W (zBlock W) = rowMean W := by
  have hz := zBlock_eq_mean_sub_covariance W hW
  calc
    zBlock W + ((m : ℝ) / a ^ 2) • covariance W (zBlock W) =
        (rowMean W - ((m : ℝ) / a ^ 2) • covariance W (zBlock W)) +
          ((m : ℝ) / a ^ 2) • covariance W (zBlock W) := by
      exact congrArg (fun x : RowSpace m ↦
        x + ((m : ℝ) / a ^ 2) • covariance W (zBlock W)) hz
    _ = rowMean W := by abel

/-- The linear operator `I + (m/a^2) Σ_W` from equation (8.5). -/
def barycentricOperator {m : ℕ} [NeZero m] (W : RowMatrix m) :
    RowSpace m →L[ℝ] RowSpace m :=
  ContinuousLinearMap.id ℝ (RowSpace m) + ((m : ℝ) / a ^ 2) • covariance W

@[simp]
theorem barycentricOperator_apply {m : ℕ} [NeZero m]
    (W : RowMatrix m) (u : RowSpace m) :
    barycentricOperator W u = u + ((m : ℝ) / a ^ 2) • covariance W u := by
  simp [barycentricOperator]

/-- Covariance equation `(I + (m/a^2) Σ_W) z_W = μ_W`, equation (8.5). -/
theorem barycentric_covariance_equation {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    barycentricOperator W (zBlock W) = rowMean W := by
  rw [barycentricOperator_apply]
  exact zBlock_add_covariance_eq_mean W hW

/-- Alias emphasizing coordinatewise positivity. -/
theorem minWeights_apply_pos {m : ℕ} [NeZero m] (W : RowMatrix m)
    (hW : Admissible W) (i : Fin m) :
    0 < (minWeights W : Fin m → ℝ) i :=
  minWeights_pos W hW i

end ZeroOrderBounds
