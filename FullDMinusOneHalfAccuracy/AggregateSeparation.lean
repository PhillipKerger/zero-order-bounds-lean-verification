import FullDMinusOneHalfAccuracy.BarycentricStability
import FullDMinusOneHalfAccuracy.SimultaneousSelections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# From aggregate row width to optimizer separation

This file is the analytic consumer of `SimultaneousSelections`.  An aggregate
directional-width lower bound first becomes a row-mean displacement.  The
almost-uniform barycentric weights then lose at most `4 tau / Gamma²`, leaving
strictly more than `tau / 5` in the selected row blocks.  Projection to the
second block gives the same separation for `minPoint`, and the sharp radial
stability theorem closes the paper's `1/600` optimizer bound.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds.AccuracyImprovement

/-- The inner product with a difference of row means is the average of the
rowwise inner-product differences. -/
theorem inner_rowMean_sub_eq_inv_mul_sum_inner_row_sub
    {m : ℕ} [NeZero m] (θ : RowSpace m) (Wplus Wminus : RowMatrix m) :
    inner ℝ θ (rowMean Wplus - rowMean Wminus) =
      (m : ℝ)⁻¹ * ∑ i, inner ℝ θ (Wplus i - Wminus i) := by
  rw [rowMean, rowMean, ← smul_sub, ← Finset.sum_sub_distrib,
    real_inner_smul_right, inner_sum]

/-- For a simultaneous extremal selection, the aggregate width is exactly
`m` times the directional displacement of the two row means. -/
theorem inner_rowMean_sub_eq_inv_mul_sum_directionalWidth
    {m : ℕ} [NeZero m] {rows : Fin m → RowBody m}
    {G : Finset (Fin m)} {θ : RowSpace m}
    (S : SimultaneousWidthSelection rows G θ) :
    inner ℝ θ (rowMean S.plus - rowMean S.minus) =
      (m : ℝ)⁻¹ *
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ := by
  rw [inner_rowMean_sub_eq_inv_mul_sum_inner_row_sub,
    sum_inner_row_sub_eq_sum_directionalWidth S]

/-- The common-direction aggregate lower bound gives a `tau / 4` row-mean
displacement. -/
theorem tau_div_four_le_inner_rowMean_sub_of_aggregate_width
    {m : ℕ} [NeZero m] {rows : Fin m → RowBody m}
    {G : Finset (Fin m)} {θ : RowSpace m}
    (S : SimultaneousWidthSelection rows G θ)
    (haggregate :
      (m : ℝ) * tau m / 4 ≤
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ) :
    tau m / 4 ≤ inner ℝ θ (rowMean S.plus - rowMean S.minus) := by
  have hm : (0 : ℝ) < (m : ℝ) := natCast_m_pos
  have hscaled := mul_le_mul_of_nonneg_left haggregate (inv_nonneg.mpr hm.le)
  rw [inner_rowMean_sub_eq_inv_mul_sum_directionalWidth S]
  calc
    tau m / 4 = (m : ℝ)⁻¹ * ((m : ℝ) * tau m / 4) := by
      field_simp [hm.ne']
    _ ≤ (m : ℝ)⁻¹ *
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ := hscaled

/-- Almost-uniform weights imply that replacing both ordinary row means by
the selected row blocks loses at most `4 tau / Gamma²` in any unit direction. -/
theorem inner_rowMean_sub_sub_four_tau_div_Gamma_sq_le_inner_zBlock_sub
    {m : ℕ} [NeZero m] (θ : RowSpace m) (hθ : ‖θ‖ = 1)
    (Wplus Wminus : RowMatrix m)
    (hWplus : Admissible Wplus) (hWminus : Admissible Wminus) :
    inner ℝ θ (rowMean Wplus - rowMean Wminus) -
        4 * tau m / Gamma ^ 2 ≤
      inner ℝ θ (zBlock Wplus - zBlock Wminus) := by
  have hplusAbs :
      |inner ℝ θ (zBlock Wplus - rowMean Wplus)| ≤
        2 * tau m / Gamma ^ 2 := by
    calc
      |inner ℝ θ (zBlock Wplus - rowMean Wplus)| ≤
          ‖θ‖ * ‖zBlock Wplus - rowMean Wplus‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖zBlock Wplus - rowMean Wplus‖ := by rw [hθ, one_mul]
      _ ≤ 2 * tau m / Gamma ^ 2 :=
        norm_zBlock_sub_rowMean_le Wplus hWplus
  have hminusAbs :
      |inner ℝ θ (zBlock Wminus - rowMean Wminus)| ≤
        2 * tau m / Gamma ^ 2 := by
    calc
      |inner ℝ θ (zBlock Wminus - rowMean Wminus)| ≤
          ‖θ‖ * ‖zBlock Wminus - rowMean Wminus‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖zBlock Wminus - rowMean Wminus‖ := by rw [hθ, one_mul]
      _ ≤ 2 * tau m / Gamma ^ 2 :=
        norm_zBlock_sub_rowMean_le Wminus hWminus
  have hplusLower :
      -(2 * tau m / Gamma ^ 2) ≤
        inner ℝ θ (zBlock Wplus - rowMean Wplus) :=
    neg_le_of_abs_le hplusAbs
  have hminusUpper :
      inner ℝ θ (zBlock Wminus - rowMean Wminus) ≤
        2 * tau m / Gamma ^ 2 :=
    le_of_abs_le hminusAbs
  have hdecomp :
      inner ℝ θ (zBlock Wplus - zBlock Wminus) =
        inner ℝ θ (rowMean Wplus - rowMean Wminus) +
          inner ℝ θ (zBlock Wplus - rowMean Wplus) -
          inner ℝ θ (zBlock Wminus - rowMean Wminus) := by
    simp only [inner_sub_right]
    ring
  have htwo :
      2 * tau m / Gamma ^ 2 + 2 * tau m / Gamma ^ 2 =
        4 * tau m / Gamma ^ 2 := by ring
  rw [hdecomp]
  rw [← htwo]
  linarith

/-- With `Gamma = 100`, the barycentric error is strictly smaller than the
gap between `tau / 4` and `tau / 5`. -/
theorem tau_div_five_lt_tau_div_four_sub_four_tau_div_Gamma_sq
    {m : ℕ} [NeZero m] :
    tau m / 5 < tau m / 4 - 4 * tau m / Gamma ^ 2 := by
  have ht : 0 < tau m := tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))
  rw [Gamma]
  norm_num
  linarith

/-- Aggregate width therefore separates the selected row blocks by more than
`tau / 5` in the common direction. -/
theorem tau_div_five_lt_inner_zBlock_sub_of_aggregate_width
    {m : ℕ} [NeZero m] {rows : Fin m → RowBody m}
    {G : Finset (Fin m)} {θ : RowSpace m} (hθ : ‖θ‖ = 1)
    (S : SimultaneousWidthSelection rows G θ)
    (haggregate :
      (m : ℝ) * tau m / 4 ≤
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ) :
    tau m / 5 < inner ℝ θ (zBlock S.plus - zBlock S.minus) := by
  have hplus : Admissible S.plus := admissible_of_mem_rowProduct S.plus_mem
  have hminus : Admissible S.minus := admissible_of_mem_rowProduct S.minus_mem
  have hmean := tau_div_four_le_inner_rowMean_sub_of_aggregate_width S haggregate
  have hz :=
    inner_rowMean_sub_sub_four_tau_div_Gamma_sq_le_inner_zBlock_sub
      θ hθ S.plus S.minus hplus hminus
  have hconstant :=
    tau_div_five_lt_tau_div_four_sub_four_tau_div_Gamma_sq (m := m)
  linarith

/-- Directional row-block separation lower-bounds separation of the full
minimum barycentric points. -/
theorem inner_zBlock_sub_le_norm_minPoint_sub
    {m : ℕ} [NeZero m] (θ : RowSpace m) (hθ : ‖θ‖ = 1)
    (Wplus Wminus : RowMatrix m) :
    inner ℝ θ (zBlock Wplus - zBlock Wminus) ≤
      ‖minPoint Wplus - minPoint Wminus‖ := by
  have hblock :
      secondBlock (minPoint Wplus - minPoint Wminus) =
        zBlock Wplus - zBlock Wminus := by
    ext i
    rfl
  calc
    inner ℝ θ (zBlock Wplus - zBlock Wminus) ≤
        |inner ℝ θ (zBlock Wplus - zBlock Wminus)| := le_abs_self _
    _ ≤ ‖θ‖ * ‖zBlock Wplus - zBlock Wminus‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖zBlock Wplus - zBlock Wminus‖ := by rw [hθ, one_mul]
    _ = ‖secondBlock (minPoint Wplus - minPoint Wminus)‖ := by rw [hblock]
    _ ≤ ‖minPoint Wplus - minPoint Wminus‖ := norm_secondBlock_le _

/-- The analytic aggregate-separation theorem for an already constructed
simultaneous selection. -/
theorem simultaneousWidthSelection_separation
    {m : ℕ} [NeZero m] {rows : Fin m → RowBody m}
    {G : Finset (Fin m)} {θ : RowSpace m} (hθ : ‖θ‖ = 1)
    (S : SimultaneousWidthSelection rows G θ)
    (haggregate :
      (m : ℝ) * tau m / 4 ≤
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ) :
    tau m / 5 < ‖minPoint S.plus - minPoint S.minus‖ ∧
      1 / 600 < ‖hardOptimizer S.plus - hardOptimizer S.minus‖ := by
  have hz := tau_div_five_lt_inner_zBlock_sub_of_aggregate_width
    hθ S haggregate
  have hmin : tau m / 5 < ‖minPoint S.plus - minPoint S.minus‖ :=
    hz.trans_le (inner_zBlock_sub_le_norm_minPoint_sub θ hθ S.plus S.minus)
  have hplus : Admissible S.plus := admissible_of_mem_rowProduct S.plus_mem
  have hminus : Admissible S.minus := admissible_of_mem_rowProduct S.minus_mem
  exact ⟨hmin,
    norm_hardOptimizer_sub_gt_one_div_600_of_norm_minPoint_sub_gt_tau_div_five
      S.plus S.minus hplus hminus hmin⟩

/-- End-to-end simultaneous construction from an aggregate-width witness.
The returned matrices retain their product-membership and complement-agreement
certificates together with both separation estimates. -/
theorem exists_aggregate_separated_matrices
    {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (G : Finset (Fin m)) (θ : RowSpace m) (hθ : ‖θ‖ = 1)
    (haggregate :
      (m : ℝ) * tau m / 4 ≤
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ) :
    ∃ Wplus Wminus : RowMatrix m,
      Wplus ∈ rowProduct rows ∧
      Wminus ∈ rowProduct rows ∧
      (∀ i, i ∉ G → Wplus i = Wminus i) ∧
      (∀ i ∈ G,
        directionalWidth (rows i : Set (RowSpace m)) θ =
          inner ℝ θ (Wplus i - Wminus i)) ∧
      tau m / 4 ≤ inner ℝ θ (rowMean Wplus - rowMean Wminus) ∧
      tau m / 5 < inner ℝ θ (zBlock Wplus - zBlock Wminus) ∧
      tau m / 5 < ‖minPoint Wplus - minPoint Wminus‖ ∧
      1 / 600 < ‖hardOptimizer Wplus - hardOptimizer Wminus‖ := by
  let S := Classical.choice (exists_simultaneousWidthSelection rows G θ)
  have hmean := tau_div_four_le_inner_rowMean_sub_of_aggregate_width S haggregate
  have hz := tau_div_five_lt_inner_zBlock_sub_of_aggregate_width hθ S haggregate
  have hsep := simultaneousWidthSelection_separation hθ S haggregate
  exact ⟨S.plus, S.minus, S.plus_mem, S.minus_mem, S.agree_of_not_mem,
    S.width_eq, hmean, hz, hsep.1, hsep.2⟩

end ZeroOrderBounds.AccuracyImprovement
