import ZeroOrderBounds.Barycentric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Sensitivity to changing one row

This module proves that changing one admissible row by `h` moves the unique
optimizer by at least a fixed multiple of `‖h‖ / √m`.  The proof first uses
the covariance equation to separate the unnormalized row blocks.  It then
controls normalization through the fixed first-block coordinate sum.
-/

noncomputable section

namespace ZeroOrderBounds

/-- The difference between two admissible versions of one row is at most twice
the row radius. -/
theorem norm_perturbation_le_two_tau {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖h‖ ≤ 2 * tau m := by
  have hj := hW j
  have hj' := hW' j
  rw [perturbRow_same] at hj'
  calc
    ‖h‖ = ‖(W j + h) - W j‖ := by simp
    _ ≤ ‖W j + h‖ + ‖W j‖ := norm_sub_le _ _
    _ ≤ tau m + tau m := add_le_add hj' hj
    _ = 2 * tau m := by ring

/-- At the chosen scale, the covariance perturbation error in the fixed-point
equation is at most one quarter of the mean perturbation. -/
theorem scaled_eight_tau_sq_le_quarter {m : ℕ} [NeZero m] :
    (m : ℝ) / a ^ 2 * (8 * tau m / (m : ℝ)) * tau m ≤
      1 / (4 * (m : ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  rw [tau, Gamma, a]
  field_simp
  nlinarith

/-- At the chosen scale, the covariance part of the barycentric operator has
norm at most one half. -/
theorem scaled_four_tau_sq_le_half {m : ℕ} [NeZero m] :
    (m : ℝ) / a ^ 2 * (4 * tau m ^ 2) ≤ 1 / 2 := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  rw [tau, Gamma, a]
  field_simp
  nlinarith

/-- Subtracting the two covariance equations gives equation (9.4). -/
theorem barycentricOperator_perturbation_equation {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    barycentricOperator (perturbRow W j h)
        (zBlock (perturbRow W j h) - zBlock W) =
      ((m : ℝ)⁻¹) • h -
        ((m : ℝ) / a ^ 2) •
          ((covariance (perturbRow W j h) - covariance W) (zBlock W)) := by
  have hEq := zBlock_add_covariance_eq_mean W hW
  have hEq' := zBlock_add_covariance_eq_mean (perturbRow W j h) hW'
  rw [rowMean_perturbRow] at hEq'
  have hcross :
      zBlock W + ((m : ℝ) / a ^ 2) •
          covariance (perturbRow W j h) (zBlock W) =
        rowMean W + ((m : ℝ) / a ^ 2) •
          ((covariance (perturbRow W j h) - covariance W) (zBlock W)) := by
    rw [← hEq]
    simp only [sub_apply]
    module
  calc
    barycentricOperator (perturbRow W j h)
        (zBlock (perturbRow W j h) - zBlock W) =
        (zBlock (perturbRow W j h) + ((m : ℝ) / a ^ 2) •
            covariance (perturbRow W j h) (zBlock (perturbRow W j h))) -
          (zBlock W + ((m : ℝ) / a ^ 2) •
            covariance (perturbRow W j h) (zBlock W)) := by
      rw [barycentricOperator_apply, map_sub, smul_sub]
      module
    _ = (rowMean W + ((m : ℝ)⁻¹) • h) -
        (rowMean W + ((m : ℝ) / a ^ 2) •
          ((covariance (perturbRow W j h) - covariance W) (zBlock W))) := by
      rw [hEq', hcross]
    _ = ((m : ℝ)⁻¹) • h -
        ((m : ℝ) / a ^ 2) •
          ((covariance (perturbRow W j h) - covariance W) (zBlock W)) := by
      module

/-- The covariance-error term in equation (9.4) is quantitatively small. -/
theorem norm_covariance_error_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖((m : ℝ) / a ^ 2) •
        ((covariance (perturbRow W j h) - covariance W) (zBlock W))‖ ≤
      ‖h‖ / (4 * (m : ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hc : 0 < (m : ℝ) / a ^ 2 :=
    div_pos hm (sq_pos_of_pos a_pos)
  have ht : 0 ≤ tau m :=
    (tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))).le
  have hcov := norm_covariance_perturbRow_sub_le W j h hW hW'
  have hz := norm_zBlock_le_tau W hW
  have happ :=
    (covariance (perturbRow W j h) - covariance W).le_opNorm (zBlock W)
  calc
    ‖((m : ℝ) / a ^ 2) •
        ((covariance (perturbRow W j h) - covariance W) (zBlock W))‖ =
        ((m : ℝ) / a ^ 2) *
          ‖(covariance (perturbRow W j h) - covariance W) (zBlock W)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    _ ≤ ((m : ℝ) / a ^ 2) *
        (‖covariance (perturbRow W j h) - covariance W‖ * ‖zBlock W‖) :=
      mul_le_mul_of_nonneg_left happ hc.le
    _ ≤ ((m : ℝ) / a ^ 2) *
        ((8 * tau m * ‖h‖ / (m : ℝ)) * tau m) := by
      gcongr
    _ = ((m : ℝ) / a ^ 2 * (8 * tau m / (m : ℝ)) * tau m) * ‖h‖ := by
      ring
    _ ≤ (1 / (4 * (m : ℝ))) * ‖h‖ :=
      mul_le_mul_of_nonneg_right scaled_eight_tau_sq_le_quarter (norm_nonneg h)
    _ = ‖h‖ / (4 * (m : ℝ)) := by ring

/-- The perturbed barycentric operator expands norms by at most `3/2`. -/
theorem norm_barycentricOperator_perturbRow_apply_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h u : RowSpace m)
    (hW' : Admissible (perturbRow W j h)) :
    ‖barycentricOperator (perturbRow W j h) u‖ ≤ (3 / 2 : ℝ) * ‖u‖ := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hc : 0 ≤ (m : ℝ) / a ^ 2 :=
    (div_pos hm (sq_pos_of_pos a_pos)).le
  have hcov := norm_covariance_le (perturbRow W j h) hW'
  have happ := (covariance (perturbRow W j h)).le_opNorm u
  rw [barycentricOperator_apply]
  calc
    ‖u + ((m : ℝ) / a ^ 2) • covariance (perturbRow W j h) u‖ ≤
        ‖u‖ + ‖((m : ℝ) / a ^ 2) • covariance (perturbRow W j h) u‖ :=
      norm_add_le _ _
    _ = ‖u‖ + ((m : ℝ) / a ^ 2) *
        ‖covariance (perturbRow W j h) u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ ‖u‖ + ((m : ℝ) / a ^ 2) *
        (‖covariance (perturbRow W j h)‖ * ‖u‖) := by
      gcongr
    _ ≤ ‖u‖ + ((m : ℝ) / a ^ 2) *
        ((4 * tau m ^ 2) * ‖u‖) := by
      gcongr
    _ = (1 + ((m : ℝ) / a ^ 2) * (4 * tau m ^ 2)) * ‖u‖ := by
      ring
    _ ≤ (1 + (1 / 2 : ℝ)) * ‖u‖ := by
      gcongr
      exact scaled_four_tau_sq_le_half
    _ = (3 / 2 : ℝ) * ‖u‖ := by ring

/-- Changing one admissible row by `h` separates the unnormalized row blocks
by at least `‖h‖ / (2m)`, equation (9.7). -/
theorem norm_zBlock_perturbRow_sub_lower {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖h‖ / (2 * (m : ℝ)) ≤
      ‖zBlock (perturbRow W j h) - zBlock W‖ := by
  let d := zBlock (perturbRow W j h) - zBlock W
  let e := ((m : ℝ) / a ^ 2) •
    ((covariance (perturbRow W j h) - covariance W) (zBlock W))
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hinv : 0 ≤ ((m : ℝ)⁻¹) := inv_nonneg.mpr hm.le
  have heq := barycentricOperator_perturbation_equation W j h hW hW'
  have herr : ‖e‖ ≤ ‖h‖ / (4 * (m : ℝ)) :=
    norm_covariance_error_le W j h hW hW'
  have hmean : ‖((m : ℝ)⁻¹) • h‖ = ‖h‖ / (m : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    rw [div_eq_mul_inv, mul_comm]
  have hreverse : ‖((m : ℝ)⁻¹) • h‖ ≤
      ‖((m : ℝ)⁻¹) • h - e‖ + ‖e‖ :=
    norm_le_norm_sub_add _ _
  have hlower : 3 * ‖h‖ / (4 * (m : ℝ)) ≤
      ‖barycentricOperator (perturbRow W j h) d‖ := by
    rw [heq] at ⊢
    rw [hmean] at hreverse
    dsimp only [e] at hreverse herr
    calc
      3 * ‖h‖ / (4 * (m : ℝ)) =
          ‖h‖ / (m : ℝ) - ‖h‖ / (4 * (m : ℝ)) := by
        field_simp [ne_of_gt hm]
        ring
      _ ≤ ‖((m : ℝ)⁻¹) • h -
            ((m : ℝ) / a ^ 2) •
              ((covariance (perturbRow W j h) - covariance W) (zBlock W))‖ := by
        linarith
  have hupper : ‖barycentricOperator (perturbRow W j h) d‖ ≤
      (3 / 2 : ℝ) * ‖d‖ :=
    norm_barycentricOperator_perturbRow_apply_le W j h d hW'
  have hchain := hlower.trans hupper
  dsimp only [d] at hchain ⊢
  calc
    ‖h‖ / (2 * (m : ℝ)) =
        (2 / 3 : ℝ) * (3 * ‖h‖ / (4 * (m : ℝ))) := by
      field_simp [ne_of_gt hm]
      ring
    _ ≤ (2 / 3 : ℝ) *
        ((3 / 2 : ℝ) *
          ‖zBlock (perturbRow W j h) - zBlock W‖) := by
      gcongr
    _ = ‖zBlock (perturbRow W j h) - zBlock W‖ := by ring

/-- Separation of the second blocks implies separation of the full minimum
points, equation (9.8). -/
theorem norm_minPoint_perturbRow_sub_lower {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖h‖ / (2 * (m : ℝ)) ≤
      ‖minPoint (perturbRow W j h) - minPoint W‖ := by
  have hblock : secondBlock
      (minPoint (perturbRow W j h) - minPoint W) =
      zBlock (perturbRow W j h) - zBlock W := by
    ext i
    rfl
  calc
    ‖h‖ / (2 * (m : ℝ)) ≤
        ‖zBlock (perturbRow W j h) - zBlock W‖ :=
      norm_zBlock_perturbRow_sub_lower W j h hW hW'
    _ = ‖secondBlock (minPoint (perturbRow W j h) - minPoint W)‖ := by
      rw [hblock]
    _ ≤ ‖minPoint (perturbRow W j h) - minPoint W‖ :=
      norm_secondBlock_le _

/-- The positively normalized minimum-norm barycentric point. -/
def normalizedMinPoint {m : ℕ} [NeZero m] (W : RowMatrix m) : QuerySpace m :=
  (‖minPoint W‖)⁻¹ • minPoint W

@[simp]
theorem norm_normalizedMinPoint {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ‖normalizedMinPoint W‖ = 1 := by
  rw [normalizedMinPoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_minPoint_pos W))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (minPoint_ne_zero W))

@[simp]
theorem coordinateSum_normalizedMinPoint {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    coordinateSum (normalizedMinPoint W) = (‖minPoint W‖)⁻¹ * a := by
  rw [normalizedMinPoint, coordinateSum_smul, coordinateSum_minPoint]

/-- Recover the unnormalized minimum point from its positive normalization. -/
theorem norm_smul_normalizedMinPoint {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    ‖minPoint W‖ • normalizedMinPoint W = minPoint W := by
  rw [normalizedMinPoint, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (minPoint_ne_zero W)), one_smul]

/-- The hard optimizer is the negative of the positive normalization. -/
theorem hardOptimizer_eq_neg_normalizedMinPoint {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    hardOptimizer W = -normalizedMinPoint W := by
  rw [hardOptimizer, normalizedMinPoint]
  simp only [neg_smul]

/-- The fixed coordinate sum controls the change in normalization radii,
equation (9.9). -/
theorem abs_norm_minPoint_perturbRow_sub_norm_minPoint_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    |‖minPoint (perturbRow W j h)‖ - ‖minPoint W‖| ≤
      4 * a / Real.sqrt (m : ℝ) *
        ‖normalizedMinPoint (perturbRow W j h) - normalizedMinPoint W‖ := by
  let W' := perturbRow W j h
  let r := ‖minPoint W‖
  let r' := ‖minPoint W'‖
  let v := normalizedMinPoint W
  let v' := normalizedMinPoint W'
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hr : 0 < r := norm_minPoint_pos W
  have hr' : 0 < r' := norm_minPoint_pos W'
  have hrUpper : r ≤ 2 * a / Real.sqrt (m : ℝ) :=
    norm_minPoint_le_two_a_div_sqrt W hW
  have hr'Upper : r' ≤ 2 * a / Real.sqrt (m : ℝ) :=
    norm_minPoint_le_two_a_div_sqrt W' hW'
  have hsum := abs_coordinateSum_le (v' - v)
  have hinvabs : a * |r'⁻¹ - r⁻¹| ≤
      Real.sqrt (m : ℝ) * ‖v' - v‖ := by
    dsimp only [v, v', r, r', W'] at ⊢ hsum
    rw [coordinateSum_sub, coordinateSum_normalizedMinPoint,
      coordinateSum_normalizedMinPoint] at hsum
    calc
      a * |‖minPoint (perturbRow W j h)‖⁻¹ - ‖minPoint W‖⁻¹| =
          |(‖minPoint (perturbRow W j h)‖⁻¹ -
            ‖minPoint W‖⁻¹) * a| := by
        rw [abs_mul, abs_of_pos a_pos]
        ring
      _ = |‖minPoint (perturbRow W j h)‖⁻¹ * a -
          ‖minPoint W‖⁻¹ * a| := by
        congr 1
        ring
      _ ≤ Real.sqrt (m : ℝ) *
          ‖normalizedMinPoint (perturbRow W j h) - normalizedMinPoint W‖ :=
        hsum
  have hinvabs' : |r'⁻¹ - r⁻¹| ≤
      Real.sqrt (m : ℝ) * ‖v' - v‖ / a := by
    apply (le_div_iff₀ a_pos).2
    simpa [mul_comm] using hinvabs
  have hdiff : |r' - r| = r * r' * |r'⁻¹ - r⁻¹| := by
    have halg : r * r' * (r'⁻¹ - r⁻¹) = r - r' := by
      field_simp [hr.ne', hr'.ne']
    calc
      |r' - r| = |r - r'| := abs_sub_comm r' r
      _ = |r * r' * (r'⁻¹ - r⁻¹)| := by rw [halg]
      _ = r * r' * |r'⁻¹ - r⁻¹| := by
        rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hr']
  have hUpperNonneg : 0 ≤ 2 * a / Real.sqrt (m : ℝ) :=
    (div_pos (mul_pos (by norm_num) a_pos) hs).le
  have hrr : r * r' ≤
      (2 * a / Real.sqrt (m : ℝ)) *
        (2 * a / Real.sqrt (m : ℝ)) :=
    mul_le_mul hrUpper hr'Upper hr'.le hUpperNonneg
  calc
    |r' - r| = r * r' * |r'⁻¹ - r⁻¹| := hdiff
    _ ≤ r * r' *
        (Real.sqrt (m : ℝ) * ‖v' - v‖ / a) :=
      mul_le_mul_of_nonneg_left hinvabs' (mul_nonneg hr.le hr'.le)
    _ ≤ ((2 * a / Real.sqrt (m : ℝ)) *
        (2 * a / Real.sqrt (m : ℝ))) *
          (Real.sqrt (m : ℝ) * ‖v' - v‖ / a) := by
      exact mul_le_mul_of_nonneg_right hrr
        (div_nonneg (mul_nonneg hs.le (norm_nonneg _)) a_pos.le)
    _ = 4 * a / Real.sqrt (m : ℝ) * ‖v' - v‖ := by
      field_simp [hs.ne', ne_of_gt a_pos]
      ring

/-- Normalization can enlarge the inverse separation by at most the factor
`6a / √m`, equation (9.10). -/
theorem norm_minPoint_perturbRow_sub_le_normalized {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖minPoint (perturbRow W j h) - minPoint W‖ ≤
      6 * a / Real.sqrt (m : ℝ) *
        ‖normalizedMinPoint (perturbRow W j h) - normalizedMinPoint W‖ := by
  let W' := perturbRow W j h
  let r := ‖minPoint W‖
  let r' := ‖minPoint W'‖
  let v := normalizedMinPoint W
  let v' := normalizedMinPoint W'
  have hr'Upper : r' ≤ 2 * a / Real.sqrt (m : ℝ) :=
    norm_minPoint_le_two_a_div_sqrt W' hW'
  have hdecomp : minPoint W' - minPoint W =
      r' • (v' - v) + (r' - r) • v := by
    have hp := norm_smul_normalizedMinPoint W
    have hp' := norm_smul_normalizedMinPoint W'
    calc
      minPoint W' - minPoint W =
          ‖minPoint W'‖ • normalizedMinPoint W' -
            ‖minPoint W‖ • normalizedMinPoint W :=
        congrArg₂ (fun x y : QuerySpace m ↦ x - y) hp'.symm hp.symm
      _ = r' • (v' - v) + (r' - r) • v := by
        dsimp only [r, r', v, v']
        module
  have hradius :=
    abs_norm_minPoint_perturbRow_sub_norm_minPoint_le W j h hW hW'
  calc
    ‖minPoint W' - minPoint W‖ =
        ‖r' • (v' - v) + (r' - r) • v‖ := by rw [hdecomp]
    _ ≤ ‖r' • (v' - v)‖ + ‖(r' - r) • v‖ := norm_add_le _ _
    _ = r' * ‖v' - v‖ + |r' - r| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (norm_minPoint_pos W'), norm_normalizedMinPoint, mul_one]
    _ ≤ (2 * a / Real.sqrt (m : ℝ)) * ‖v' - v‖ +
        (4 * a / Real.sqrt (m : ℝ)) * ‖v' - v‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hr'Upper (norm_nonneg _)
      · simpa only [W', r, r', v, v'] using hradius
    _ = 6 * a / Real.sqrt (m : ℝ) * ‖v' - v‖ := by ring

/-- The quantitative one-row sensitivity theorem, equation (9.12). -/
theorem hardOptimizer_perturbRow_separation {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖h‖ / (16 * a * Real.sqrt (m : ℝ)) ≤
      ‖hardOptimizer W - hardOptimizer (perturbRow W j h)‖ := by
  let W' := perturbRow W j h
  let D := ‖normalizedMinPoint W' - normalizedMinPoint W‖
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  have hsep := norm_minPoint_perturbRow_sub_lower W j h hW hW'
  have hnorm := norm_minPoint_perturbRow_sub_le_normalized W j h hW hW'
  have hD : ‖h‖ / (12 * a * Real.sqrt (m : ℝ)) ≤ D := by
    dsimp only [W', D] at ⊢ hsep hnorm
    have hc : 0 < 6 * a / Real.sqrt (m : ℝ) :=
      div_pos (mul_pos (by norm_num) a_pos) hs
    have hmul :
        (6 * a / Real.sqrt (m : ℝ)) *
            (‖h‖ / (12 * a * Real.sqrt (m : ℝ))) ≤
          (6 * a / Real.sqrt (m : ℝ)) *
            ‖normalizedMinPoint (perturbRow W j h) - normalizedMinPoint W‖ := by
      calc
        (6 * a / Real.sqrt (m : ℝ)) *
            (‖h‖ / (12 * a * Real.sqrt (m : ℝ))) =
            ‖h‖ / (2 * (m : ℝ)) := by
          field_simp [hs.ne', ne_of_gt a_pos]
          rw [hs2]
          ring
        _ ≤ ‖minPoint (perturbRow W j h) - minPoint W‖ := hsep
        _ ≤ (6 * a / Real.sqrt (m : ℝ)) *
            ‖normalizedMinPoint (perturbRow W j h) - normalizedMinPoint W‖ :=
          hnorm
    exact le_of_mul_le_mul_left hmul hc
  have hweaker : ‖h‖ / (16 * a * Real.sqrt (m : ℝ)) ≤ D := by
    have hH : 0 ≤ ‖h‖ := norm_nonneg h
    have hden : 0 < a * Real.sqrt (m : ℝ) := mul_pos a_pos hs
    calc
      ‖h‖ / (16 * a * Real.sqrt (m : ℝ)) ≤
          ‖h‖ / (12 * a * Real.sqrt (m : ℝ)) := by
        gcongr <;> nlinarith
      _ ≤ D := hD
  have hoptimizer :
      ‖hardOptimizer W - hardOptimizer W'‖ = D := by
    rw [hardOptimizer_eq_neg_normalizedMinPoint,
      hardOptimizer_eq_neg_normalizedMinPoint]
    dsimp only [D]
    calc
      ‖-normalizedMinPoint W - -normalizedMinPoint W'‖ =
          ‖-(normalizedMinPoint W - normalizedMinPoint W')‖ := by
        congr 1
        module
      _ = ‖normalizedMinPoint W - normalizedMinPoint W'‖ := norm_neg _
      _ = ‖normalizedMinPoint W' - normalizedMinPoint W‖ := norm_sub_rev _ _
  rw [hoptimizer]
  exact hweaker

/-- Equivalent `≥`-oriented headline statement. -/
theorem norm_hardOptimizer_sub_perturbRow_ge {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖hardOptimizer W - hardOptimizer (perturbRow W j h)‖ ≥
      ‖h‖ / (16 * a * Real.sqrt (m : ℝ)) :=
  hardOptimizer_perturbRow_separation W j h hW hW'

end ZeroOrderBounds
