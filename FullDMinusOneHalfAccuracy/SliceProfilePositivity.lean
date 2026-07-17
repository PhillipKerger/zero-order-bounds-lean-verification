import FullDMinusOneHalfAccuracy.BrunnMinkowskiSliceProfiles

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Positivity of the slice-radius profile

A nonnegative concave function on an interval which is positive somewhere
is positive throughout the open interval.  Combined with Cavalieri, this
shows that every interior slice of a positive-volume convex body has
positive volume radius.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ZeroOrderBounds.AccuracyImprovement

/-- A nonnegative concave function which is positive at one point of a
closed interval is positive at every interior point. -/
theorem ConcaveOn.pos_of_pos_at_of_mem_Ioo
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc a b) f)
    (hnonneg : ∀ y ∈ Icc a b, 0 ≤ f y)
    {z : ℝ} (hz : z ∈ Icc a b) (hfz : 0 < f z)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < f x := by
  rcases lt_trichotomy x z with hxz | rfl | hzx
  · let α : ℝ := (z - x) / (z - a)
    let β : ℝ := (x - a) / (z - a)
    have hza : 0 < z - a := sub_pos.mpr (hx.1.trans hxz)
    have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hxz.le) hza.le
    have hβ : 0 < β := div_pos (sub_pos.mpr hx.1) hza
    have hsum : α + β = 1 := by
      dsimp [α, β]
      field_simp
      ring
    have hcoord : α • a + β • z = x := by
      simp only [smul_eq_mul]
      dsimp [α, β]
      field_simp
      ring
    have hconc := hf.2 (left_mem_Icc.mpr (hz.1.trans hz.2)) hz hα hβ.le hsum
    rw [hcoord] at hconc
    have hleft : 0 < α • f a + β • f z := by
      simp only [smul_eq_mul]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg hα (hnonneg a (left_mem_Icc.mpr (hz.1.trans hz.2))))
        (mul_pos hβ hfz)
    exact hleft.trans_le hconc
  · exact hfz
  · let α : ℝ := (b - x) / (b - z)
    let β : ℝ := (x - z) / (b - z)
    have hbz : 0 < b - z := sub_pos.mpr (hzx.trans hx.2)
    have hα : 0 < α := div_pos (sub_pos.mpr hx.2) hbz
    have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hzx.le) hbz.le
    have hsum : α + β = 1 := by
      dsimp [α, β]
      field_simp
      ring
    have hcoord : α • z + β • b = x := by
      simp only [smul_eq_mul]
      dsimp [α, β]
      field_simp
      ring
    have hconc := hf.2 hz (right_mem_Icc.mpr (hz.1.trans hz.2)) hα.le hβ hsum
    rw [hcoord] at hconc
    have hleft : 0 < α • f z + β • f b := by
      simp only [smul_eq_mul]
      exact add_pos_of_pos_of_nonneg
        (mul_pos hα hfz)
        (mul_nonneg hβ (hnonneg b (right_mem_Icc.mpr (hz.1.trans hz.2))))
    exact hleft.trans_le hconc

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Positive total volume forces at least one slice to have positive real
volume. -/
theorem exists_sliceVolumeReal_pos (K : ConvexBody (ℝ × V))
    (hKvol : 0 < (volume (K : Set (ℝ × V))).toReal) :
    ∃ z : ℝ, 0 < sliceVolumeReal K z := by
  by_contra h
  push Not at h
  have hzero : sliceVolumeReal K = 0 := by
    funext z
    exact le_antisymm (h z) (sliceVolumeReal_nonneg K z)
  rw [convexBodyVolumeReal_eq_integral_sliceVolumeReal K, hzero] at hKvol
  simp at hKvol

/-- The positive slice found by Cavalieri lies in the projection interval. -/
theorem exists_mem_Icc_sliceVolumeReal_pos (K : ConvexBody (ℝ × V))
    (hKvol : 0 < (volume (K : Set (ℝ × V))).toReal) :
    ∃ z ∈ Icc (sliceLeftEndpoint K) (sliceRightEndpoint K),
      0 < sliceVolumeReal K z := by
  obtain ⟨z, hzpos⟩ := exists_sliceVolumeReal_pos K hKvol
  have hzne : (verticalSlice (K : Set (ℝ × V)) z).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro hempty
    rw [sliceVolumeReal, hempty, measure_empty, ENNReal.toReal_zero] at hzpos
    exact hzpos.false
  exact ⟨z, (verticalSlice_nonempty_iff_mem_Icc K z).1 hzne, hzpos⟩

/-- Every interior slice-radius is strictly positive for a positive-volume
body, provided the fiber dimension is positive and Brunn--Minkowski is known
in the fiber. -/
theorem sliceVolumeRadius_pos_on_Ioo
    (hBM : ∀ (t : ℝ) (A B : ConvexBody V),
      0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t A B)
    (K : ConvexBody (ℝ × V))
    (hKvol : 0 < (volume (K : Set (ℝ × V))).toReal) :
    ∀ x ∈ Ioo (sliceLeftEndpoint K) (sliceRightEndpoint K),
      0 < sliceVolumeRadius K x := by
  obtain ⟨z, hz, hzpos⟩ := exists_mem_Icc_sliceVolumeReal_pos K hKvol
  have hrz : 0 < sliceVolumeRadius K z := by
    exact Real.rpow_pos_of_pos hzpos _
  exact fun x hx ↦ ConcaveOn.pos_of_pos_at_of_mem_Ioo
    (concaveOn_sliceVolumeRadius hBM K)
    (fun y _ ↦ sliceVolumeRadius_nonneg K y) hz hrz hx

end ZeroOrderBounds.AccuracyImprovement
