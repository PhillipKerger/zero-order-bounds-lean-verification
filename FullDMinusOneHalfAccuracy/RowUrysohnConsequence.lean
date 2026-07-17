import FullDMinusOneHalfAccuracy.UrysohnAssembly
import FullDMinusOneHalfAccuracy.RowProjectionBridge
import ZeroOrderBounds.VolumePotential

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Row-level consequence of intrinsic Urysohn

This file performs the normalization algebra connecting intrinsic volume to
the row potential.  Its endpoint is exactly the hypothesis consumed by
`ConditionalMain`.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- A row whose normalized volume radius is larger than `1/2` has intrinsic
mean width at least `tau`.  The only geometric premise is midpoint
Brunn--Minkowski in the standard Euclidean coordinates of this row's affine
hull. -/
theorem tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius
    {m : ℕ} [NeZero m] (P : RowBody m) (hdim : 0 < P.dim)
    (hBM : ∀ K L : ConvexBody
        (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ P.body.directionSpan))),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (hradius : (1 / 2 : ℝ) <
      P.normalizedVolume ^ (((P.dim : ℕ) : ℝ)⁻¹)) :
    tau m ≤ positiveIntrinsicMeanWidth P hdim := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have htau : 0 < tau m := tau_pos hm
  have hdim_ne : P.body.dim ≠ 0 := by
    simpa [RowBody.dim] using hdim.ne'
  letI : Nontrivial P.body.directionSpan :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_directionSpan_eq_dim]
      exact hdim)
  have hury := two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth
    P.body hdim_ne hBM
  change 2 * (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) ≤
      intrinsicMeanWidth P.body P.body.directionSpan at hury
  change tau m ≤ intrinsicMeanWidth P.body P.body.directionSpan
  have hkappa : 0 < kappaReal P.dim := kappaReal_pos P.dim
  have htauPow : 0 < tau m ^ P.dim := pow_pos htau P.dim
  have hfactor :
      P.volumeReal / kappaReal P.dim =
        P.normalizedVolume * tau m ^ P.dim := by
    rw [RowBody.normalizedVolume]
    field_simp [hkappa.ne', htauPow.ne']
  have hnormalized : 0 ≤ P.normalizedVolume :=
    (P.normalizedVolume_pos hm).le
  have hrootFactor :
      (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) =
        P.normalizedVolume ^ ((P.dim : ℝ)⁻¹) * tau m := by
    rw [hfactor,
      Real.mul_rpow hnormalized (pow_nonneg htau.le P.dim),
      Real.pow_rpow_inv_natCast htau.le hdim.ne']
  have htau_lt :
      tau m <
        2 * (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) := by
    rw [hrootFactor]
    have hmul := mul_lt_mul_of_pos_right hradius htau
    nlinarith
  exact htau_lt.le.trans hury

end ZeroOrderBounds.AccuracyImprovement
