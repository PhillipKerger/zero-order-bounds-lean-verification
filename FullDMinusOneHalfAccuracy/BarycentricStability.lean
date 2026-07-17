import ZeroOrderBounds.Barycentric
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Sharp barycentric stability for the improved-accuracy argument

This file packages the quantitative consequences of the exact barycentric
stationarity formula proved in `ZeroOrderBounds.Barycentric`.  In particular,
it records the constants used by the aggregate-width branch of the paper:

* every minimizing weight is within `2 / (Gamma ^ 2 * m)` of the uniform
  weight;
* the minimum barycentric point has the sharp squared-norm upper bound
  `(a ^ 2 / m) * (1 + (Gamma ^ 2)⁻¹)`; and
* its norm lies in the corresponding sharp interval.

The final group of lemmas separates radial and angular variation.  They are
stated first for arbitrary real normed spaces and then specialized to
`minPoint` and `hardOptimizer`, so the later aggregate-separation proof does
not have to repeat normalization algebra.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- The definition of `tau` in squared form, with the dimension and `Gamma`
factors separated. -/
theorem tau_sq_eq_sharp {m : ℕ} [NeZero m] :
    tau m ^ 2 =
      (a ^ 2 / (m : ℝ)) * (Gamma ^ 2)⁻¹ := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  rw [tau, div_pow, mul_pow, hs2]
  field_simp [Gamma_pos.ne', hm.ne']

/-- The norm of a centered row is at most twice the admissible row radius. -/
theorem norm_rowMean_sub_row_le_two_tau {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    ‖rowMean W - W i‖ ≤ 2 * tau m := by
  calc
    ‖rowMean W - W i‖ ≤ ‖rowMean W‖ + ‖W i‖ := norm_sub_le _ _
    _ ≤ tau m + tau m := add_le_add (norm_rowMean_le_tau W hW) (hW i)
    _ = 2 * tau m := by ring

/-- The correction in the explicit barycentric-weight formula is bounded by
`2 tau² / a²`. -/
theorem abs_minWeights_sub_inv_nat_le_two_tau_sq_div_a_sq
    {m : ℕ} [NeZero m] (W : RowMatrix m) (hW : Admissible W)
    (i : Fin m) :
    |(minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹| ≤
      2 * tau m ^ 2 / a ^ 2 := by
  have hinner :
      |inner ℝ (rowMean W - W i) (zBlock W)| ≤
        (2 * tau m) * tau m := by
    calc
      |inner ℝ (rowMean W - W i) (zBlock W)| ≤
          ‖rowMean W - W i‖ * ‖zBlock W‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2 * tau m) * tau m := by
        exact mul_le_mul (norm_rowMean_sub_row_le_two_tau W hW i)
          (norm_zBlock_le_tau W hW) (norm_nonneg _)
          (mul_nonneg (by norm_num) (tau_pos
            (Nat.pos_of_ne_zero (NeZero.ne m))).le)
  rw [minWeights_apply_eq W hW i, add_sub_cancel_left]
  rw [abs_div, abs_of_pos (sq_pos_of_pos a_pos)]
  calc
    |inner ℝ (rowMean W - W i) (zBlock W)| / a ^ 2 ≤
        ((2 * tau m) * tau m) / a ^ 2 := by
      exact div_le_div_of_nonneg_right hinner (sq_nonneg a)
    _ = 2 * tau m ^ 2 / a ^ 2 := by ring

/-- Equation (8.3) plus admissibility gives the paper's almost-uniform
barycentric weights. -/
theorem abs_minWeights_sub_inv_nat_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    |(minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹| ≤
      2 / (Gamma ^ 2 * (m : ℝ)) := by
  calc
    |(minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹| ≤
        2 * tau m ^ 2 / a ^ 2 :=
      abs_minWeights_sub_inv_nat_le_two_tau_sq_div_a_sq W hW i
    _ = 2 / (Gamma ^ 2 * (m : ℝ)) := by
      rw [tau_sq_eq_sharp]
      have ha : a ^ 2 ≠ 0 := pow_ne_zero _ a_pos.ne'
      have hG : Gamma ^ 2 ≠ 0 := pow_ne_zero _ Gamma_pos.ne'
      have hm : (m : ℝ) ≠ 0 := natCast_m_ne_zero
      field_simp [ha, hG, hm, a_pos.ne']

/-- Symmetric interval form of almost-uniformity. -/
theorem minWeights_mem_Icc_uniform {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    (minWeights W : Fin m → ℝ) i ∈
      Set.Icc ((m : ℝ)⁻¹ - 2 / (Gamma ^ 2 * (m : ℝ)))
        ((m : ℝ)⁻¹ + 2 / (Gamma ^ 2 * (m : ℝ))) := by
  have h := (abs_le.mp (abs_minWeights_sub_inv_nat_le W hW i))
  constructor <;> linarith

/-- The selected row block differs from the ordinary row mean by at most
`2 tau / Gamma²`.  This is the summed form of coordinatewise almost-uniformity
used in aggregate separation. -/
theorem norm_zBlock_sub_rowMean_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖zBlock W - rowMean W‖ ≤ 2 * tau m / Gamma ^ 2 := by
  have hdecomp :
      zBlock W - rowMean W =
        ∑ i, (((minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹) • W i) := by
    rw [zBlock_eq_weightedRow, weightedRow, rowMean, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [sub_smul]
  have hcoeff : 0 ≤ 2 / (Gamma ^ 2 * (m : ℝ)) := by
    exact div_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg Gamma) (Nat.cast_nonneg m))
  rw [hdecomp]
  calc
    ‖∑ i, (((minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹) • W i)‖ ≤
        ∑ i, ‖((minWeights W : Fin m → ℝ) i - (m : ℝ)⁻¹) • W i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, (2 / (Gamma ^ 2 * (m : ℝ))) * tau m := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (abs_minWeights_sub_inv_nat_le W hW i) (hW i)
        (norm_nonneg _) hcoeff
    _ = 2 * tau m / Gamma ^ 2 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hm : (m : ℝ) ≠ 0 := natCast_m_ne_zero
      have hG : Gamma ^ 2 ≠ 0 := pow_ne_zero _ Gamma_pos.ne'
      field_simp [hm, hG]

/-- Sharp squared-norm estimate for the minimum barycentric point. -/
theorem norm_minPoint_sq_le_sharp {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ^ 2 ≤
      (a ^ 2 / (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹) := by
  calc
    ‖minPoint W‖ ^ 2 ≤ a ^ 2 / (m : ℝ) + tau m ^ 2 :=
      norm_minPoint_sq_le W hW
    _ = (a ^ 2 / (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹) := by
      rw [tau_sq_eq_sharp]
      ring

/-- Sharp norm estimate obtained by taking the nonnegative square root of
`norm_minPoint_sq_le_sharp`. -/
theorem norm_minPoint_le_sharp {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ≤
      (a / Real.sqrt (m : ℝ)) *
        Real.sqrt (1 + (Gamma ^ 2)⁻¹) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  have hfactor : 0 ≤ 1 + (Gamma ^ 2)⁻¹ :=
    add_nonneg zero_le_one (inv_nonneg.mpr (sq_nonneg Gamma))
  have hfactor2 : Real.sqrt (1 + (Gamma ^ 2)⁻¹) ^ 2 =
      1 + (Gamma ^ 2)⁻¹ := Real.sq_sqrt hfactor
  have hrhs_nonneg :
      0 ≤ (a / Real.sqrt (m : ℝ)) *
        Real.sqrt (1 + (Gamma ^ 2)⁻¹) :=
    mul_nonneg (div_nonneg a_pos.le hs.le) (Real.sqrt_nonneg _)
  have hrhs_sq :
      ((a / Real.sqrt (m : ℝ)) *
          Real.sqrt (1 + (Gamma ^ 2)⁻¹)) ^ 2 =
        (a ^ 2 / (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹) := by
    rw [mul_pow, div_pow, hs2, hfactor2]
  have hsq := norm_minPoint_sq_le_sharp W hW
  rw [← hrhs_sq] at hsq
  nlinarith [norm_nonneg (minPoint W)]

/-- Complete sharp interval for the norm of the minimum barycentric point. -/
theorem norm_minPoint_mem_Icc_sharp {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ∈
      Set.Icc (a / Real.sqrt (m : ℝ))
        ((a / Real.sqrt (m : ℝ)) *
          Real.sqrt (1 + (Gamma ^ 2)⁻¹)) :=
  ⟨a_div_sqrt_le_norm_minPoint W, norm_minPoint_le_sharp W hW⟩

/-! ## Radial versus angular separation -/

/-- Decompose the distance between two nonzero vectors into angular motion at
the radius of the first vector and a purely radial error. -/
theorem norm_sub_le_norm_mul_norm_normalize_sub_add_abs_norm_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hy : y ≠ 0) :
    ‖x - y‖ ≤
      ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ +
        |‖x‖ - ‖y‖| := by
  have hxrecover := NormedSpace.norm_smul_normalize x
  have hyrecover := NormedSpace.norm_smul_normalize y
  have hdecomp :
      ‖x‖ • NormedSpace.normalize x -
          ‖y‖ • NormedSpace.normalize y =
        ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) +
          (‖x‖ - ‖y‖) • NormedSpace.normalize y := by
    module
  calc
    ‖x - y‖ =
        ‖‖x‖ • NormedSpace.normalize x -
          ‖y‖ • NormedSpace.normalize y‖ := by
      rw [hxrecover, hyrecover]
    _ = ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) +
          (‖x‖ - ‖y‖) • NormedSpace.normalize y‖ := by rw [hdecomp]
    _ ≤ ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ +
          ‖(‖x‖ - ‖y‖) • NormedSpace.normalize y‖ := norm_add_le _ _
    _ = ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ +
          |‖x‖ - ‖y‖| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x), NormedSpace.norm_normalize hy,
        mul_one]

/-- If both radii lie in `[r, R]`, their vector distance is at most `R` times
their angular distance plus the interval width `R - r`. -/
theorem norm_sub_le_upper_mul_norm_normalize_sub_add_width
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {r R : ℝ} (hr : 0 < r)
    (hxr : r ≤ ‖x‖) (hxR : ‖x‖ ≤ R)
    (hyr : r ≤ ‖y‖) (hyR : ‖y‖ ≤ R) :
    ‖x - y‖ ≤
      R * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ + (R - r) := by
  have hy : y ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hyr))
  have hradius : |‖x‖ - ‖y‖| ≤ R - r := by
    rw [abs_le]
    constructor <;> linarith
  calc
    ‖x - y‖ ≤
        ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ +
          |‖x‖ - ‖y‖| :=
      norm_sub_le_norm_mul_norm_normalize_sub_add_abs_norm_sub x y hy
    _ ≤ R * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ +
          (R - r) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hxR (norm_nonneg _)) hradius

/-- Rearranged strict form of
`norm_sub_le_upper_mul_norm_normalize_sub_add_width`. -/
theorem norm_normalize_sub_gt_of_norm_sub_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {r R delta : ℝ} (hr : 0 < r)
    (hxr : r ≤ ‖x‖) (hxR : ‖x‖ ≤ R)
    (hyr : r ≤ ‖y‖) (hyR : ‖y‖ ≤ R)
    (hsep : delta < ‖x - y‖) :
    (delta - (R - r)) / R <
      ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := by
  have hR : 0 < R := hr.trans_le (hxr.trans hxR)
  have hbound := norm_sub_le_upper_mul_norm_normalize_sub_add_width
    x y hr hxr hxR hyr hyR
  apply (div_lt_iff₀ hR).2
  nlinarith

/-- For the present hard family, `hardOptimizer` is the negative normalized
minimum barycentric point. -/
theorem hardOptimizer_eq_neg_normalize_minPoint {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    hardOptimizer W = -NormedSpace.normalize (minPoint W) := by
  rw [hardOptimizer, NormedSpace.normalize]
  simp only [neg_smul]

/-- Normalized minimum-point distance is exactly optimizer distance (the
common negative sign is an isometry). -/
theorem norm_normalize_minPoint_sub_eq_norm_hardOptimizer_sub
    {m : ℕ} [NeZero m] (W₁ W₂ : RowMatrix m) :
    ‖NormedSpace.normalize (minPoint W₁) -
        NormedSpace.normalize (minPoint W₂)‖ =
      ‖hardOptimizer W₁ - hardOptimizer W₂‖ := by
  rw [hardOptimizer_eq_neg_normalize_minPoint,
    hardOptimizer_eq_neg_normalize_minPoint]
  calc
    ‖NormedSpace.normalize (minPoint W₁) -
        NormedSpace.normalize (minPoint W₂)‖ =
        ‖-(NormedSpace.normalize (minPoint W₁) -
          NormedSpace.normalize (minPoint W₂))‖ := (norm_neg _).symm
    _ = ‖-NormedSpace.normalize (minPoint W₁) -
          -NormedSpace.normalize (minPoint W₂)‖ := by
      congr 1
      module

/-- Sharp radial/angular decomposition specialized to two admissible hard
instances. -/
theorem norm_minPoint_sub_le_sharp_mul_norm_hardOptimizer_sub_add_width
    {m : ℕ} [NeZero m] (W₁ W₂ : RowMatrix m)
    (hW₁ : Admissible W₁) (hW₂ : Admissible W₂) :
    ‖minPoint W₁ - minPoint W₂‖ ≤
      ((a / Real.sqrt (m : ℝ)) * Real.sqrt (1 + (Gamma ^ 2)⁻¹)) *
          ‖hardOptimizer W₁ - hardOptimizer W₂‖ +
        ((a / Real.sqrt (m : ℝ)) * Real.sqrt (1 + (Gamma ^ 2)⁻¹) -
          a / Real.sqrt (m : ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hlo : 0 < a / Real.sqrt (m : ℝ) :=
    div_pos a_pos (Real.sqrt_pos.2 hm)
  have h := norm_sub_le_upper_mul_norm_normalize_sub_add_width
    (minPoint W₁) (minPoint W₂) hlo
    (a_div_sqrt_le_norm_minPoint W₁) (norm_minPoint_le_sharp W₁ hW₁)
    (a_div_sqrt_le_norm_minPoint W₂) (norm_minPoint_le_sharp W₂ hW₂)
  rw [norm_normalize_minPoint_sub_eq_norm_hardOptimizer_sub] at h
  exact h

/-- A minimum-point separation yields an explicit optimizer separation after
subtracting the worst possible radial drift. -/
theorem norm_hardOptimizer_sub_gt_of_norm_minPoint_sub_gt
    {m : ℕ} [NeZero m] (W₁ W₂ : RowMatrix m)
    (hW₁ : Admissible W₁) (hW₂ : Admissible W₂) {delta : ℝ}
    (hsep : delta < ‖minPoint W₁ - minPoint W₂‖) :
    (delta -
        (((a / Real.sqrt (m : ℝ)) * Real.sqrt (1 + (Gamma ^ 2)⁻¹)) -
          a / Real.sqrt (m : ℝ))) /
        ((a / Real.sqrt (m : ℝ)) * Real.sqrt (1 + (Gamma ^ 2)⁻¹)) <
      ‖hardOptimizer W₁ - hardOptimizer W₂‖ := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hlo : 0 < a / Real.sqrt (m : ℝ) :=
    div_pos a_pos (Real.sqrt_pos.2 hm)
  have h := norm_normalize_sub_gt_of_norm_sub_gt
    (minPoint W₁) (minPoint W₂) hlo
    (a_div_sqrt_le_norm_minPoint W₁) (norm_minPoint_le_sharp W₁ hW₁)
    (a_div_sqrt_le_norm_minPoint W₂) (norm_minPoint_le_sharp W₂ hW₂) hsep
  rw [norm_normalize_minPoint_sub_eq_norm_hardOptimizer_sub] at h
  exact h

/-! ## Concrete constants for aggregate separation -/

/-- The elementary concavity estimate used to replace the sharp radical by a
rational upper bound. -/
theorem sqrt_one_add_inv_Gamma_sq_le :
    Real.sqrt (1 + (Gamma ^ 2)⁻¹) ≤
      1 + (Gamma ^ 2)⁻¹ / 2 := by
  have hx : 0 ≤ (Gamma ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg Gamma)
  have hbase : 0 ≤ 1 + (Gamma ^ 2)⁻¹ := add_nonneg zero_le_one hx
  have hs : 0 ≤ Real.sqrt (1 + (Gamma ^ 2)⁻¹) := Real.sqrt_nonneg _
  have hr : 0 ≤ 1 + (Gamma ^ 2)⁻¹ / 2 := by linarith
  have hs2 : Real.sqrt (1 + (Gamma ^ 2)⁻¹) ^ 2 =
      1 + (Gamma ^ 2)⁻¹ := Real.sq_sqrt hbase
  nlinarith [sq_nonneg ((Gamma ^ 2)⁻¹)]

/-- A rational relaxation of `norm_minPoint_le_sharp`, convenient for closing
the final numerical comparison. -/
theorem norm_minPoint_le_rational_sharp {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ≤
      (a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  calc
    ‖minPoint W‖ ≤
        (a / Real.sqrt (m : ℝ)) *
          Real.sqrt (1 + (Gamma ^ 2)⁻¹) := norm_minPoint_le_sharp W hW
    _ ≤ (a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) :=
      mul_le_mul_of_nonneg_left sqrt_one_add_inv_Gamma_sq_le
        (div_nonneg a_pos.le (Real.sqrt_nonneg _))

/-- Rational radial/angular decomposition for two admissible hard instances. -/
theorem norm_minPoint_sub_le_rational_mul_norm_hardOptimizer_sub_add_width
    {m : ℕ} [NeZero m] (W₁ W₂ : RowMatrix m)
    (hW₁ : Admissible W₁) (hW₂ : Admissible W₂) :
    ‖minPoint W₁ - minPoint W₂‖ ≤
      ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2)) *
          ‖hardOptimizer W₁ - hardOptimizer W₂‖ +
        ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) -
          a / Real.sqrt (m : ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hlo : 0 < a / Real.sqrt (m : ℝ) :=
    div_pos a_pos (Real.sqrt_pos.2 hm)
  have h := norm_sub_le_upper_mul_norm_normalize_sub_add_width
    (minPoint W₁) (minPoint W₂) hlo
    (a_div_sqrt_le_norm_minPoint W₁) (norm_minPoint_le_rational_sharp W₁ hW₁)
    (a_div_sqrt_le_norm_minPoint W₂) (norm_minPoint_le_rational_sharp W₂ hW₂)
  rw [norm_normalize_minPoint_sub_eq_norm_hardOptimizer_sub] at h
  exact h

/-- At `Gamma = 100`, angular distance `1/600` together with the entire
possible radial drift is still smaller than `tau / 5`. -/
theorem rational_radial_error_at_one_div_600_le_tau_div_five
    {m : ℕ} [NeZero m] :
    ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2)) * (1 / 600) +
        ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) -
          a / Real.sqrt (m : ℝ)) ≤
      tau m / 5 := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  rw [tau, a, Gamma]
  field_simp [hs.ne']
  norm_num

/-- The exact aggregate endgame: separation of minimum points by more than
`tau / 5` forces the paper's `1/600` optimizer separation. -/
theorem norm_hardOptimizer_sub_gt_one_div_600_of_norm_minPoint_sub_gt_tau_div_five
    {m : ℕ} [NeZero m] (W₁ W₂ : RowMatrix m)
    (hW₁ : Admissible W₁) (hW₂ : Admissible W₂)
    (hsep : tau m / 5 < ‖minPoint W₁ - minPoint W₂‖) :
    1 / 600 < ‖hardOptimizer W₁ - hardOptimizer W₂‖ := by
  by_contra hnot
  have hangular : ‖hardOptimizer W₁ - hardOptimizer W₂‖ ≤ 1 / 600 :=
    le_of_not_gt hnot
  have hdecomp :=
    norm_minPoint_sub_le_rational_mul_norm_hardOptimizer_sub_add_width
      W₁ W₂ hW₁ hW₂
  have hscale :
      0 ≤ (a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) := by
    have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
    have hG : 0 ≤ (Gamma ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg Gamma)
    exact mul_nonneg (div_nonneg a_pos.le (Real.sqrt_nonneg _)) (by linarith)
  have hupper :
      ‖minPoint W₁ - minPoint W₂‖ ≤
        ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2)) * (1 / 600) +
          ((a / Real.sqrt (m : ℝ)) * (1 + (Gamma ^ 2)⁻¹ / 2) -
            a / Real.sqrt (m : ℝ)) := by
    exact hdecomp.trans (add_le_add
      (mul_le_mul_of_nonneg_left hangular hscale) le_rfl)
  have hconstant := rational_radial_error_at_one_div_600_le_tau_div_five
    (m := m)
  linarith

end ZeroOrderBounds.AccuracyImprovement
