import ZeroOrderBounds.HardFamily
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Means and covariance operators for row matrices

This module packages the finite-dimensional operator algebra needed by the
one-row sensitivity argument.  Covariance is represented without coordinates,
as an average of rank-one continuous linear maps.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds

open InnerProductSpace

/-- Polarization-free difference identity for two rank-one squares. -/
theorem rankOne_self_sub (x y : RowSpace m) :
    rankOne ℝ x x - rankOne ℝ y y =
      rankOne ℝ (x - y) x + rankOne ℝ y (x - y) := by
  ext u i
  simp [rankOne_apply]

/-- Norm control for a difference of rank-one squares. -/
theorem norm_rankOne_self_sub_le (x y : RowSpace m) :
    ‖rankOne ℝ x x - rankOne ℝ y y‖ ≤
      ‖x - y‖ * (‖x‖ + ‖y‖) := by
  rw [rankOne_self_sub]
  calc
    ‖rankOne ℝ (x - y) x + rankOne ℝ y (x - y)‖ ≤
        ‖rankOne ℝ (x - y) x‖ + ‖rankOne ℝ y (x - y)‖ :=
      norm_add_le _ _
    _ = ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := by
      rw [norm_rankOne, norm_rankOne]
    _ = ‖x - y‖ * (‖x‖ + ‖y‖) := by ring

@[simp]
theorem rankOne_add_left (x y z : RowSpace m) :
    rankOne ℝ (x + y) z = rankOne ℝ x z + rankOne ℝ y z := by
  ext u
  simp [rankOne_apply]

@[simp]
theorem rankOne_sub_left (x y z : RowSpace m) :
    rankOne ℝ (x - y) z = rankOne ℝ x z - rankOne ℝ y z := by
  ext u
  simp [rankOne_apply]

@[simp]
theorem rankOne_add_right (x y z : RowSpace m) :
    rankOne ℝ x (y + z) = rankOne ℝ x y + rankOne ℝ x z := by
  ext u
  simp [rankOne_apply]

@[simp]
theorem rankOne_sub_right (x y z : RowSpace m) :
    rankOne ℝ x (y - z) = rankOne ℝ x y - rankOne ℝ x z := by
  ext u
  simp [rankOne_apply]

@[simp]
theorem rankOne_smul_left (c : ℝ) (x y : RowSpace m) :
    rankOne ℝ (c • x) y = c • rankOne ℝ x y := by
  ext u
  simp [rankOne_apply, smul_smul]

@[simp]
theorem rankOne_smul_right (c : ℝ) (x y : RowSpace m) :
    rankOne ℝ x (c • y) = c • rankOne ℝ x y := by
  ext u
  simp [rankOne_apply, smul_smul, mul_comm]

theorem sum_rankOne_left {n : ℕ} (f : Fin n → RowSpace m) (y : RowSpace m) :
    ∑ i, rankOne ℝ (f i) y = rankOne ℝ (∑ i, f i) y := by
  ext u
  simp [rankOne_apply]

theorem sum_rankOne_right {n : ℕ} (x : RowSpace m) (f : Fin n → RowSpace m) :
    ∑ i, rankOne ℝ x (f i) = rankOne ℝ x (∑ i, f i) := by
  ext u
  simp [rankOne_apply]

/-- Arithmetic mean of the rows. -/
def rowMean {m : ℕ} [NeZero m] (W : RowMatrix m) : RowSpace m :=
  ((m : ℝ)⁻¹) • ∑ i, W i

/-- A row centered at the arithmetic mean. -/
def centeredRow {m : ℕ} [NeZero m] (W : RowMatrix m) (i : Fin m) : RowSpace m :=
  W i - rowMean W

/-- Empirical covariance operator of the rows. -/
def covariance {m : ℕ} [NeZero m] (W : RowMatrix m) :
    RowSpace m →L[ℝ] RowSpace m :=
  ((m : ℝ)⁻¹) •
    ∑ i, InnerProductSpace.rankOne ℝ (centeredRow W i) (centeredRow W i)

/-- Replace row `j` by `W j + h`.  This is the canonical one-row
perturbation used by the sensitivity theorem. -/
def perturbRow {m : ℕ} (W : RowMatrix m) (j : Fin m) (h : RowSpace m) :
    RowMatrix m :=
  Function.update W j (W j + h)

@[simp]
theorem perturbRow_same {m : ℕ} (W : RowMatrix m) (j : Fin m) (h : RowSpace m) :
    perturbRow W j h j = W j + h := by
  simp [perturbRow]

theorem perturbRow_of_ne {m : ℕ} (W : RowMatrix m) (j i : Fin m)
    (h : RowSpace m) (hi : i ≠ j) :
    perturbRow W j h i = W i := by
  simp [perturbRow, hi]

theorem perturbRow_sub_apply {m : ℕ} (W : RowMatrix m) (j i : Fin m)
    (h : RowSpace m) :
    perturbRow W j h i - W i = if i = j then h else 0 := by
  classical
  by_cases hi : i = j
  · subst i
    simp
  · simp [perturbRow, hi]

theorem natCast_m_ne_zero {m : ℕ} [NeZero m] : (m : ℝ) ≠ 0 := by
  exact_mod_cast NeZero.ne m

theorem natCast_m_pos {m : ℕ} [NeZero m] : (0 : ℝ) < m := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

/-- A one-row perturbation changes the row sum by exactly `h`. -/
theorem sum_perturbRow {m : ℕ} [NeZero m] (W : RowMatrix m)
    (j : Fin m) (h : RowSpace m) :
    ∑ i, perturbRow W j h i = (∑ i, W i) + h := by
  classical
  simp only [perturbRow, Finset.sum_update_of_mem (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin m)).erase j, W i) + W j =
      ∑ i, W i :=
    Finset.sum_erase_add Finset.univ W (Finset.mem_univ j)
  rw [← hsum]
  abel

/-- A one-row perturbation changes the mean by `h / m`. -/
theorem rowMean_perturbRow {m : ℕ} [NeZero m] (W : RowMatrix m)
    (j : Fin m) (h : RowSpace m) :
    rowMean (perturbRow W j h) = rowMean W + ((m : ℝ)⁻¹) • h := by
  simp only [rowMean, sum_perturbRow, smul_add]

/-- Centering commutes with a one-row perturbation up to the common mean shift. -/
theorem centeredRow_perturbRow_sub {m : ℕ} [NeZero m] (W : RowMatrix m)
    (j i : Fin m) (h : RowSpace m) :
    centeredRow (perturbRow W j h) i - centeredRow W i =
      (perturbRow W j h i - W i) - ((m : ℝ)⁻¹) • h := by
  rw [centeredRow, centeredRow, rowMean_perturbRow]
  abel

theorem centeredRow_perturbRow {m : ℕ} [NeZero m] (W : RowMatrix m)
    (j i : Fin m) (h : RowSpace m) :
    centeredRow (perturbRow W j h) i =
      centeredRow W i + (if i = j then h else 0) - ((m : ℝ)⁻¹) • h := by
  have hd := centeredRow_perturbRow_sub W j i h
  rw [perturbRow_sub_apply] at hd
  calc
    centeredRow (perturbRow W j h) i =
        (centeredRow (perturbRow W j h) i - centeredRow W i) +
          centeredRow W i := by abel
    _ = ((if i = j then h else 0) - ((m : ℝ)⁻¹) • h) +
          centeredRow W i := by rw [hd]
    _ = centeredRow W i + (if i = j then h else 0) -
          ((m : ℝ)⁻¹) • h := by abel

/-- The total rowwise displacement of `perturbRow` is exactly the size of `h`. -/
theorem sum_norm_perturbRow_sub {m : ℕ} [NeZero m] (W : RowMatrix m)
    (j : Fin m) (h : RowSpace m) :
    ∑ i, ‖perturbRow W j h i - W i‖ = ‖h‖ := by
  classical
  calc
    ∑ i, ‖perturbRow W j h i - W i‖ =
        ‖perturbRow W j h j - W j‖ := by
      apply Finset.sum_eq_single j
      · intro i _ hi
        simp [perturbRow, hi]
      · simp
    _ = ‖h‖ := by simp

/-- The sum of changes of all centered rows is at most twice the changed-row norm. -/
theorem sum_norm_centeredRow_perturbRow_sub_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m) :
    ∑ i, ‖centeredRow (perturbRow W j h) i - centeredRow W i‖ ≤ 2 * ‖h‖ := by
  calc
    ∑ i, ‖centeredRow (perturbRow W j h) i - centeredRow W i‖ =
        ∑ i, ‖(perturbRow W j h i - W i) - ((m : ℝ)⁻¹) • h‖ := by
      congr 1
      funext i
      rw [centeredRow_perturbRow_sub]
    _ ≤ ∑ i, (‖perturbRow W j h i - W i‖ + ‖((m : ℝ)⁻¹) • h‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sub_le _ _
    _ = ‖h‖ + (m : ℝ) * ((m : ℝ)⁻¹ * ‖h‖) := by
      rw [Finset.sum_add_distrib, sum_norm_perturbRow_sub]
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr natCast_m_pos), Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    _ = 2 * ‖h‖ := by
      have hm0 := natCast_m_ne_zero (m := m)
      field_simp
      ring

/-- Multiplying the mean by the number of rows recovers their sum. -/
theorem natCast_smul_rowMean {m : ℕ} [NeZero m] (W : RowMatrix m) :
    (m : ℝ) • rowMean W = ∑ i, W i := by
  simp [rowMean, smul_smul]

/-- The centered rows sum to zero. -/
theorem sum_centeredRow {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ∑ i, centeredRow W i = 0 := by
  rw [show (∑ i, centeredRow W i) = (∑ i, W i) - (m : ℝ) • rowMean W by
    simp [centeredRow, Finset.sum_sub_distrib, Nat.cast_smul_eq_nsmul]]
  rw [natCast_smul_rowMean]
  simp

/-- Expanding centered rank-one squares gives raw second moment minus the
rank-one square of the mean. -/
theorem sum_rankOne_centered_eq {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ∑ i, rankOne ℝ (centeredRow W i) (centeredRow W i) =
      (∑ i, rankOne ℝ (W i) (W i)) -
        (m : ℝ) • rankOne ℝ (rowMean W) (rowMean W) := by
  simp only [centeredRow, rankOne_sub_left, rankOne_sub_right,
    Finset.sum_sub_distrib]
  rw [sum_rankOne_left, sum_rankOne_right, ← natCast_smul_rowMean]
  simp only [rankOne_smul_left, rankOne_smul_right,
    Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  module

/-- Covariance as raw second moment minus the rank-one square of the mean. -/
theorem covariance_eq_raw_second_moment {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    covariance W =
      ((m : ℝ)⁻¹) • (∑ i, rankOne ℝ (W i) (W i)) -
        rankOne ℝ (rowMean W) (rowMean W) := by
  rw [covariance, sum_rankOne_centered_eq, smul_sub, smul_smul]
  have hm0 := natCast_m_ne_zero (m := m)
  rw [inv_mul_cancel₀ hm0, one_smul]

/-- Exact change of the raw second moment under a one-row perturbation. -/
theorem sum_rankOne_perturbRow_sub {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m) :
    (∑ i, rankOne ℝ (perturbRow W j h i) (perturbRow W j h i)) -
        ∑ i, rankOne ℝ (W i) (W i) =
      rankOne ℝ (W j) h + rankOne ℝ h (W j) + rankOne ℝ h h := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i, (rankOne ℝ (perturbRow W j h i) (perturbRow W j h i) -
        rankOne ℝ (W i) (W i)) =
        rankOne ℝ (perturbRow W j h j) (perturbRow W j h j) -
          rankOne ℝ (W j) (W j) := by
      apply Finset.sum_eq_single j
      · intro i _ hi
        rw [perturbRow_of_ne W j i h hi]
        simp
      · simp
    _ = rankOne ℝ (W j) h + rankOne ℝ h (W j) + rankOne ℝ h h := by
      rw [perturbRow_same, rankOne_add_left]
      simp only [rankOne_add_right]
      abel

/-- Exact one-row covariance perturbation identity (formula (9.2) in the
formalization plan). -/
theorem covariance_perturbRow_sub {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m) :
    covariance (perturbRow W j h) - covariance W =
      ((m : ℝ)⁻¹) •
        (rankOne ℝ (centeredRow W j) h +
          rankOne ℝ h (centeredRow W j) +
          (1 - (m : ℝ)⁻¹) • rankOne ℝ h h) := by
  rw [covariance_eq_raw_second_moment, covariance_eq_raw_second_moment]
  calc
    (((m : ℝ)⁻¹) •
          (∑ i, rankOne ℝ (perturbRow W j h i) (perturbRow W j h i)) -
        rankOne ℝ (rowMean (perturbRow W j h)) (rowMean (perturbRow W j h))) -
      (((m : ℝ)⁻¹) • (∑ i, rankOne ℝ (W i) (W i)) -
        rankOne ℝ (rowMean W) (rowMean W)) =
        ((m : ℝ)⁻¹) •
          ((∑ i, rankOne ℝ (perturbRow W j h i) (perturbRow W j h i)) -
            ∑ i, rankOne ℝ (W i) (W i)) -
          (rankOne ℝ (rowMean (perturbRow W j h)) (rowMean (perturbRow W j h)) -
            rankOne ℝ (rowMean W) (rowMean W)) := by module
    _ = ((m : ℝ)⁻¹) •
        (rankOne ℝ (centeredRow W j) h +
          rankOne ℝ h (centeredRow W j) +
          (1 - (m : ℝ)⁻¹) • rankOne ℝ h h) := by
      rw [sum_rankOne_perturbRow_sub, rowMean_perturbRow]
      simp only [centeredRow, rankOne_add_left, rankOne_add_right,
        rankOne_sub_left, rankOne_sub_right, rankOne_smul_left,
        rankOne_smul_right]
      module

@[simp]
theorem covariance_apply {m : ℕ} [NeZero m] (W : RowMatrix m) (u : RowSpace m) :
    covariance W u =
      ((m : ℝ)⁻¹) • ∑ i, inner ℝ (centeredRow W i) u • centeredRow W i := by
  simp [covariance]

/-- Covariance is positive semidefinite. -/
theorem inner_covariance_nonneg {m : ℕ} [NeZero m]
    (W : RowMatrix m) (u : RowSpace m) :
    0 ≤ inner ℝ (covariance W u) u := by
  rw [covariance_apply, real_inner_smul_left]
  simp only [sum_inner, real_inner_smul_left]
  apply mul_nonneg (inv_nonneg.mpr natCast_m_pos.le)
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (inner ℝ (centeredRow W i) u)

/-- The mean of admissible rows remains in the same centered ball. -/
theorem norm_rowMean_le_tau {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖rowMean W‖ ≤ tau m := by
  calc
    ‖rowMean W‖ = ((m : ℝ)⁻¹) * ‖∑ i, W i‖ := by
      rw [rowMean, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr natCast_m_pos)]
    _ ≤ ((m : ℝ)⁻¹) * ∑ i, ‖W i‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ((m : ℝ)⁻¹) * ∑ _i : Fin m, tau m := by
      gcongr with i
      exact hW i
    _ = tau m := by
      simp only [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
      rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ natCast_m_ne_zero, one_mul]

/-- Every centered admissible row has norm at most twice the row radius. -/
theorem norm_centeredRow_le_two_tau {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    ‖centeredRow W i‖ ≤ 2 * tau m := by
  calc
    ‖centeredRow W i‖ ≤ ‖W i‖ + ‖rowMean W‖ := by
      simpa [centeredRow] using norm_sub_le (W i) (rowMean W)
    _ ≤ tau m + tau m := add_le_add (hW i) (norm_rowMean_le_tau W hW)
    _ = 2 * tau m := by ring

/-- Operator-norm covariance bound used throughout the sensitivity proof. -/
theorem norm_covariance_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖covariance W‖ ≤ 4 * tau m ^ 2 := by
  rw [covariance, norm_smul]
  have hinvnorm : ‖((m : ℝ)⁻¹)‖ = (m : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr natCast_m_pos)]
  rw [hinvnorm]
  calc
    (m : ℝ)⁻¹ * ‖∑ i, InnerProductSpace.rankOne ℝ
        (centeredRow W i) (centeredRow W i)‖
        ≤ (m : ℝ)⁻¹ * ∑ i, ‖InnerProductSpace.rankOne ℝ
          (centeredRow W i) (centeredRow W i)‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ (m : ℝ)⁻¹ * ∑ _i : Fin m, 4 * tau m ^ 2 := by
      gcongr with i
      rw [InnerProductSpace.norm_rankOne]
      have hi := norm_centeredRow_le_two_tau W hW i
      have ht : 0 ≤ tau m := (tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))).le
      nlinarith [norm_nonneg (centeredRow W i)]
    _ = 4 * tau m ^ 2 := by
      simp only [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
      rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ natCast_m_ne_zero, one_mul]

/-- A one-row change perturbs covariance by at most `8 τ ‖h‖ / m`.

The manuscript records the slightly sharper constant `6`; the present bound
has ample slack for the subsequent sensitivity estimate and follows directly
from the centered-row representation. -/
theorem norm_covariance_perturbRow_sub_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (j : Fin m) (h : RowSpace m)
    (hW : Admissible W) (hW' : Admissible (perturbRow W j h)) :
    ‖covariance (perturbRow W j h) - covariance W‖ ≤
      8 * tau m * ‖h‖ / (m : ℝ) := by
  have ht : 0 ≤ tau m :=
    (tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))).le
  have hinv : 0 ≤ ((m : ℝ)⁻¹) := inv_nonneg.mpr natCast_m_pos.le
  rw [covariance, covariance]
  have hfactor :
      ((m : ℝ)⁻¹) •
          (∑ i, rankOne ℝ (centeredRow (perturbRow W j h) i)
            (centeredRow (perturbRow W j h) i)) -
        ((m : ℝ)⁻¹) • (∑ i, rankOne ℝ (centeredRow W i) (centeredRow W i)) =
      ((m : ℝ)⁻¹) •
        ((∑ i, rankOne ℝ (centeredRow (perturbRow W j h) i)
            (centeredRow (perturbRow W j h) i)) -
          ∑ i, rankOne ℝ (centeredRow W i) (centeredRow W i)) := by
    exact (smul_sub _ _ _).symm
  rw [hfactor, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr natCast_m_pos)]
  calc
    (m : ℝ)⁻¹ *
        ‖(∑ i, rankOne ℝ (centeredRow (perturbRow W j h) i)
              (centeredRow (perturbRow W j h) i)) -
          ∑ i, rankOne ℝ (centeredRow W i) (centeredRow W i)‖ =
      (m : ℝ)⁻¹ *
        ‖∑ i, (rankOne ℝ (centeredRow (perturbRow W j h) i)
              (centeredRow (perturbRow W j h) i) -
            rankOne ℝ (centeredRow W i) (centeredRow W i))‖ := by
        rw [Finset.sum_sub_distrib]
    _ ≤ (m : ℝ)⁻¹ *
        ∑ i, ‖rankOne ℝ (centeredRow (perturbRow W j h) i)
              (centeredRow (perturbRow W j h) i) -
            rankOne ℝ (centeredRow W i) (centeredRow W i)‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv
    _ ≤ (m : ℝ)⁻¹ *
        ∑ i, ‖centeredRow (perturbRow W j h) i - centeredRow W i‖ *
          (4 * tau m) := by
      gcongr with i
      calc
        ‖rankOne ℝ (centeredRow (perturbRow W j h) i)
              (centeredRow (perturbRow W j h) i) -
            rankOne ℝ (centeredRow W i) (centeredRow W i)‖ ≤
            ‖centeredRow (perturbRow W j h) i - centeredRow W i‖ *
              (‖centeredRow (perturbRow W j h) i‖ + ‖centeredRow W i‖) :=
          norm_rankOne_self_sub_le _ _
        _ ≤ ‖centeredRow (perturbRow W j h) i - centeredRow W i‖ *
              (4 * tau m) := by
          gcongr
          have hleft := norm_centeredRow_le_two_tau (perturbRow W j h) hW' i
          have hright := norm_centeredRow_le_two_tau W hW i
          linarith
    _ = (m : ℝ)⁻¹ *
        ((∑ i, ‖centeredRow (perturbRow W j h) i - centeredRow W i‖) *
          (4 * tau m)) := by
      rw [Finset.sum_mul]
    _ ≤ (m : ℝ)⁻¹ * (2 * ‖h‖ * (4 * tau m)) := by
      gcongr
      exact sum_norm_centeredRow_perturbRow_sub_le W j h
    _ = 8 * tau m * ‖h‖ / (m : ℝ) := by
      rw [div_eq_mul_inv]
      ring

end ZeroOrderBounds
