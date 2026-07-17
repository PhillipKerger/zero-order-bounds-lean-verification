import FullDMinusOneHalfAccuracy.BrunnMinkowskiInduction
import FullDMinusOneHalfAccuracy.RowUrysohnConsequence

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Unconditional intrinsic Urysohn inequalities

`UrysohnAssembly` proves the sharp intrinsic inequality from midpoint
Brunn--Minkowski in the affine hull.  This module supplies that premise from
the dimension-uniform Euclidean Brunn--Minkowski theorem, exposing the
geometric result independently of the optimization endgame.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- Sharp intrinsic Urysohn inequality, with full directional mean width:
twice the intrinsic volume radius is at most the mean width. -/
theorem two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth_unconditional
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : IntrinsicBody E) [Nontrivial P.directionSpan] (hdim : P.dim ≠ 0) :
    2 * (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) ≤
      intrinsicMeanWidth P P.directionSpan := by
  apply two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth P hdim
  intro K L
  have hn : 0 < Module.finrank ℝ P.directionSpan := by
    rw [finrank_directionSpan_eq_dim]
    exact Nat.pos_of_ne_zero hdim
  exact brunnMinkowskiAt_euclidean
    (Module.finrank ℝ P.directionSpan) hn (1 / 2 : ℝ) K L
    (by norm_num) (by norm_num)

/-- Equivalent half-mean-width form of unconditional intrinsic Urysohn. -/
theorem intrinsicVolumeRadius_le_half_intrinsicMeanWidth_unconditional
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : IntrinsicBody E) [Nontrivial P.directionSpan] (hdim : P.dim ≠ 0) :
    (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) ≤
      intrinsicMeanWidth P P.directionSpan / 2 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using
    two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth_unconditional P hdim

/-- The row-body form used in the lower bound: normalized volume radius above
`1/2` forces intrinsic mean width at least `tau m`. -/
theorem tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius_unconditional
    {m : ℕ} [NeZero m] (P : RowBody m) (hdim : 0 < P.dim)
    (hradius : (1 / 2 : ℝ) <
      P.normalizedVolume ^ (((P.dim : ℕ) : ℝ)⁻¹)) :
    tau m ≤ positiveIntrinsicMeanWidth P hdim := by
  apply tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius
    P hdim _ hradius
  intro K L
  have hn : 0 < Module.finrank ℝ P.body.directionSpan := by
    rw [finrank_directionSpan_eq_dim]
    exact hdim
  exact brunnMinkowskiAt_euclidean
    (Module.finrank ℝ P.body.directionSpan) hn (1 / 2 : ℝ) K L
    (by norm_num) (by norm_num)

end ZeroOrderBounds.AccuracyImprovement
