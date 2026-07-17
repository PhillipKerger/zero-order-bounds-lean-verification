import FullDMinusOneHalfAccuracy.BrunnMinkowskiSliceProfiles

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Nondegeneracy of a positive-volume slicing interval

The slice-profile module identifies the first-coordinate projection of a
convex body with a compact interval.  This short companion proves that the
interval has positive length whenever the product volume is positive.
-/

noncomputable section

open MeasureTheory Set

namespace ZeroOrderBounds.AccuracyImprovement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Positive product volume forces distinct projection endpoints. -/
theorem sliceLeftEndpoint_lt_sliceRightEndpoint_of_volume_pos
    (K : ConvexBody (ℝ × V))
    (hvolume : 0 < volume (K : Set (ℝ × V))) :
    sliceLeftEndpoint K < sliceRightEndpoint K := by
  have hle : sliceLeftEndpoint K ≤ sliceRightEndpoint K :=
    sliceLeftEndpoint_le K (sliceRightEndpoint_mem K)
  apply hle.lt_of_ne
  intro heq
  have hae :
      (fun x : ℝ => volume (verticalSlice (K : Set (ℝ × V)) x)) =ᵐ[volume]
        (fun _x : ℝ => 0) := by
    filter_upwards [volume.ae_ne (sliceRightEndpoint K)] with x hx
    have hempty : verticalSlice (K : Set (ℝ × V)) x = ∅ := by
      rw [← not_nonempty_iff_eq_empty,
        verticalSlice_nonempty_iff_mem_Icc, heq, Icc_self]
      simpa using hx
    simp [hempty]
  have hzero : volume (K : Set (ℝ × V)) = 0 := by
    rw [volume_eq_lintegral_verticalSlice K.isCompact,
      lintegral_eq_zero_of_ae_eq_zero hae]
  exact hvolume.ne' hzero

end ZeroOrderBounds.AccuracyImprovement
