import FullDMinusOneHalfAccuracy.BrunnMinkowskiSlices
import Mathlib.Analysis.Convex.Continuous

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Slice-volume profiles for the Brunn--Minkowski induction

This is the interface between the geometric slice inclusions in
`BrunnMinkowskiSlices` and the one-dimensional density transport theorem.
It identifies the projection of a convex body with a compact interval,
defines the `(dim V)`-th root of each vertical slice volume, proves the exact
Cavalieri normalization, and derives concavity of that radius profile from
Brunn--Minkowski in `V`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ## Monotonicity of real volume roots -/

theorem convexBodyVolumeReal_mono {A B : ConvexBody V}
    (hAB : (A : Set V) ⊆ (B : Set V)) :
    convexBodyVolumeReal A ≤ convexBodyVolumeReal B := by
  apply (ENNReal.toReal_le_toReal A.isCompact.measure_lt_top.ne
    B.isCompact.measure_lt_top.ne).2
  exact measure_mono hAB

theorem convexBodyVolumeRoot_mono {A B : ConvexBody V}
    (hAB : (A : Set V) ⊆ (B : Set V)) :
    convexBodyVolumeRoot A ≤ convexBodyVolumeRoot B := by
  exact Real.rpow_le_rpow (convexBodyVolumeReal_nonneg A)
    (convexBodyVolumeReal_mono hAB)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-! ## Projection interval -/

/-- First-coordinate projection, equivalently the set of nonempty slices. -/
def firstCoordinateProjection (K : ConvexBody (ℝ × V)) : Set ℝ :=
  Prod.fst '' (K : Set (ℝ × V))

theorem isCompact_firstCoordinateProjection (K : ConvexBody (ℝ × V)) :
    IsCompact (firstCoordinateProjection K) :=
  K.isCompact.image continuous_fst

theorem firstCoordinateProjection_nonempty (K : ConvexBody (ℝ × V)) :
    (firstCoordinateProjection K).Nonempty :=
  K.nonempty.image _

theorem convex_firstCoordinateProjection (K : ConvexBody (ℝ × V)) :
    Convex ℝ (firstCoordinateProjection K) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨a • p + b • q, K.convex hp hq ha hb hab, ?_⟩
  simp

/-- Left endpoint of the projection interval. -/
def sliceLeftEndpoint (K : ConvexBody (ℝ × V)) : ℝ :=
  sInf (firstCoordinateProjection K)

/-- Right endpoint of the projection interval. -/
def sliceRightEndpoint (K : ConvexBody (ℝ × V)) : ℝ :=
  sSup (firstCoordinateProjection K)

theorem sliceLeftEndpoint_mem (K : ConvexBody (ℝ × V)) :
    sliceLeftEndpoint K ∈ firstCoordinateProjection K :=
  (isCompact_firstCoordinateProjection K).isLeast_sInf
    (firstCoordinateProjection_nonempty K) |>.1

theorem sliceRightEndpoint_mem (K : ConvexBody (ℝ × V)) :
    sliceRightEndpoint K ∈ firstCoordinateProjection K :=
  (isCompact_firstCoordinateProjection K).isGreatest_sSup
    (firstCoordinateProjection_nonempty K) |>.1

theorem sliceLeftEndpoint_le (K : ConvexBody (ℝ × V))
    {x : ℝ} (hx : x ∈ firstCoordinateProjection K) :
    sliceLeftEndpoint K ≤ x :=
  (isCompact_firstCoordinateProjection K).isLeast_sInf
    (firstCoordinateProjection_nonempty K) |>.2 hx

theorem le_sliceRightEndpoint (K : ConvexBody (ℝ × V))
    {x : ℝ} (hx : x ∈ firstCoordinateProjection K) :
    x ≤ sliceRightEndpoint K :=
  (isCompact_firstCoordinateProjection K).isGreatest_sSup
    (firstCoordinateProjection_nonempty K) |>.2 hx

theorem firstCoordinateProjection_eq_Icc (K : ConvexBody (ℝ × V)) :
    firstCoordinateProjection K =
      Icc (sliceLeftEndpoint K) (sliceRightEndpoint K) := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨sliceLeftEndpoint_le K hx, le_sliceRightEndpoint K hx⟩
  · exact (convex_firstCoordinateProjection K).ordConnected.out
      (sliceLeftEndpoint_mem K) (sliceRightEndpoint_mem K)

theorem verticalSlice_nonempty_iff_mem_projection
    (K : ConvexBody (ℝ × V)) (x : ℝ) :
    (verticalSlice (K : Set (ℝ × V)) x).Nonempty ↔
      x ∈ firstCoordinateProjection K := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(x, v), hv, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩

theorem verticalSlice_nonempty_iff_mem_Icc
    (K : ConvexBody (ℝ × V)) (x : ℝ) :
    (verticalSlice (K : Set (ℝ × V)) x).Nonempty ↔
      x ∈ Icc (sliceLeftEndpoint K) (sliceRightEndpoint K) := by
  rw [verticalSlice_nonempty_iff_mem_projection,
    firstCoordinateProjection_eq_Icc]

/-! ## Slice volumes and radii -/

/-- Real `V`-volume of the vertical slice.  Empty slices automatically have
value zero. -/
def sliceVolumeReal (K : ConvexBody (ℝ × V)) (x : ℝ) : ℝ :=
  (volume (verticalSlice (K : Set (ℝ × V)) x)).toReal

/-- The `(dim V)`-th root of the slice volume. -/
def sliceVolumeRadius (K : ConvexBody (ℝ × V)) (x : ℝ) : ℝ :=
  sliceVolumeReal K x ^ ((Module.finrank ℝ V : ℝ)⁻¹)

theorem sliceVolumeReal_nonneg (K : ConvexBody (ℝ × V)) (x : ℝ) :
    0 ≤ sliceVolumeReal K x :=
  ENNReal.toReal_nonneg

theorem sliceVolumeRadius_nonneg (K : ConvexBody (ℝ × V)) (x : ℝ) :
    0 ≤ sliceVolumeRadius K x :=
  Real.rpow_nonneg (sliceVolumeReal_nonneg K x) _

theorem sliceVolumeRadius_pow_finrank (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) (x : ℝ) :
    sliceVolumeRadius K x ^ Module.finrank ℝ V = sliceVolumeReal K x := by
  exact Real.rpow_inv_natCast_pow (sliceVolumeReal_nonneg K x) hdim

theorem sliceVolumeRadius_eq_convexBodyVolumeRoot
    (K : ConvexBody (ℝ × V)) (x : ℝ)
    (hne : (verticalSlice (K : Set (ℝ × V)) x).Nonempty) :
    sliceVolumeRadius K x = convexBodyVolumeRoot (verticalSliceBody K x hne) :=
  rfl

/-- Real-valued Cavalieri formula. -/
theorem convexBodyVolumeReal_eq_integral_sliceVolumeReal
    (K : ConvexBody (ℝ × V)) :
    (volume (K : Set (ℝ × V))).toReal =
      ∫ x : ℝ, sliceVolumeReal K x := by
  have hmeas : Measurable (fun x : ℝ ↦
      volume (verticalSlice (K : Set (ℝ × V)) x)) :=
    measurable_measure_prodMk_left K.isCompact.measurableSet
  have hfinite : ∀ x : ℝ,
      volume (verticalSlice (K : Set (ℝ × V)) x) < ∞ := by
    intro x
    exact (isCompact_verticalSlice K.isCompact x).measure_lt_top
  rw [volume_eq_lintegral_verticalSlice K.isCompact]
  exact (integral_toReal hmeas.aemeasurable
    (Filter.Eventually.of_forall hfinite)).symm

theorem convexBodyVolumeReal_eq_integral_sliceRadius_pow
    (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) :
    (volume (K : Set (ℝ × V))).toReal =
      ∫ x : ℝ, sliceVolumeRadius K x ^ Module.finrank ℝ V := by
  rw [convexBodyVolumeReal_eq_integral_sliceVolumeReal]
  congr 1
  funext x
  exact (sliceVolumeRadius_pow_finrank K hdim x).symm

theorem sliceLeftEndpoint_le_sliceRightEndpoint
    (K : ConvexBody (ℝ × V)) :
    sliceLeftEndpoint K ≤ sliceRightEndpoint K :=
  sliceLeftEndpoint_le K (sliceRightEndpoint_mem K)

theorem sliceVolumeReal_eq_zero_of_not_mem_Icc
    (K : ConvexBody (ℝ × V)) {x : ℝ}
    (hx : x ∉ Icc (sliceLeftEndpoint K) (sliceRightEndpoint K)) :
    sliceVolumeReal K x = 0 := by
  have hempty : verticalSlice (K : Set (ℝ × V)) x = ∅ :=
    not_nonempty_iff_eq_empty.mp
      (fun hne ↦ hx ((verticalSlice_nonempty_iff_mem_Icc K x).1 hne))
  simp [sliceVolumeReal, hempty]

theorem sliceVolumeRadius_eq_zero_of_not_mem_Icc
    (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) {x : ℝ}
    (hx : x ∉ Icc (sliceLeftEndpoint K) (sliceRightEndpoint K)) :
    sliceVolumeRadius K x = 0 := by
  rw [sliceVolumeRadius, sliceVolumeReal_eq_zero_of_not_mem_Icc K hx]
  exact Real.zero_rpow (by
    exact inv_ne_zero (by exact_mod_cast hdim))

/-- The slice-volume density is globally integrable. -/
theorem integrable_sliceVolumeReal (K : ConvexBody (ℝ × V)) :
    Integrable (sliceVolumeReal K) := by
  have hmeas : Measurable (fun x : ℝ ↦
      volume (verticalSlice (K : Set (ℝ × V)) x)) :=
    measurable_measure_prodMk_left K.isCompact.measurableSet
  apply integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable
  rw [← volume_eq_lintegral_verticalSlice K.isCompact]
  exact K.isCompact.measure_lt_top.ne

/-- Consequently the `dim V`-th power of the slice radius is globally
integrable (in positive slice dimension). -/
theorem integrable_sliceVolumeRadius_pow
    (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) :
    Integrable (fun x ↦ sliceVolumeRadius K x ^ Module.finrank ℝ V) :=
  (integrable_sliceVolumeReal K).congr
    (Filter.Eventually.of_forall fun x ↦
      (sliceVolumeRadius_pow_finrank K hdim x).symm)

theorem intervalIntegrable_sliceVolumeRadius_pow
    (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) :
    IntervalIntegrable
      (fun x ↦ sliceVolumeRadius K x ^ Module.finrank ℝ V)
      volume (sliceLeftEndpoint K) (sliceRightEndpoint K) :=
  (integrable_sliceVolumeRadius_pow K hdim).intervalIntegrable

/-- The interval integral over the projection interval is exactly the
ambient real volume.  Endpoint slice values are harmless because singleton
sets have Lebesgue measure zero. -/
theorem integral_sliceVolumeRadius_pow_projection
    (K : ConvexBody (ℝ × V))
    (hdim : Module.finrank ℝ V ≠ 0) :
    (∫ x in sliceLeftEndpoint K..sliceRightEndpoint K,
        sliceVolumeRadius K x ^ Module.finrank ℝ V) =
      (volume (K : Set (ℝ × V))).toReal := by
  let f : ℝ → ℝ := fun x ↦
    sliceVolumeRadius K x ^ Module.finrank ℝ V
  have hab := sliceLeftEndpoint_le_sliceRightEndpoint K
  rw [intervalIntegral.integral_of_le hab,
    ← integral_indicator measurableSet_Ioc]
  have hae : (Ioc (sliceLeftEndpoint K) (sliceRightEndpoint K)).indicator f
      =ᵐ[volume] f := by
    filter_upwards [Measure.ae_ne volume (sliceLeftEndpoint K)] with x hxa
    by_cases hx : x ∈ Ioc (sliceLeftEndpoint K) (sliceRightEndpoint K)
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      have hxIcc : x ∉ Icc (sliceLeftEndpoint K) (sliceRightEndpoint K) := by
        intro h
        exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hxa), h.2⟩
      simp only [f, sliceVolumeRadius_eq_zero_of_not_mem_Icc K hdim hxIcc,
        zero_pow hdim]
  rw [integral_congr_ae hae]
  exact (convexBodyVolumeReal_eq_integral_sliceRadius_pow K hdim).symm

/-! ## Concavity supplied by lower-dimensional Brunn--Minkowski -/

/-- The two-body pointwise slice-radius inequality.  This is the exact
geometric inequality consumed by the one-dimensional BBL theorem. -/
theorem weighted_sliceVolumeRadius_le_weightedMinkowski_of_brunnMinkowski
    (hBM : ∀ (t : ℝ) (A B : ConvexBody V),
      0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t A B)
    (K L : ConvexBody (ℝ × V)) {t x y : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hx : (verticalSlice (K : Set (ℝ × V)) x).Nonempty)
    (hy : (verticalSlice (L : Set (ℝ × V)) y).Nonempty) :
    (1 - t) * sliceVolumeRadius K x + t * sliceVolumeRadius L y ≤
      sliceVolumeRadius ((1 - t) • K + t • L)
        ((1 - t) * x + t * y) := by
  let A : ConvexBody V := verticalSliceBody K x hx
  let B : ConvexBody V := verticalSliceBody L y hy
  let M : ConvexBody (ℝ × V) := (1 - t) • K + t • L
  let z : ℝ := (1 - t) * x + t * y
  have hsource :
      ((1 - t) • A + t • B : ConvexBody V).carrier ⊆
        verticalSlice (M : Set (ℝ × V)) z := by
    exact weighted_verticalSliceBody_subset K L (t := t) hx hy
  have htarget : (verticalSlice (M : Set (ℝ × V)) z).Nonempty :=
    ((1 - t) • A + t • B).nonempty.mono hsource
  have hmono :
      convexBodyVolumeRoot ((1 - t) • A + t • B) ≤
        convexBodyVolumeRoot (verticalSliceBody M z htarget) :=
    convexBodyVolumeRoot_mono hsource
  have hbm := hBM t A B ht₀ ht₁
  rw [BrunnMinkowskiAt] at hbm
  calc
    (1 - t) * sliceVolumeRadius K x + t * sliceVolumeRadius L y =
        (1 - t) * convexBodyVolumeRoot A + t * convexBodyVolumeRoot B := by
      rw [sliceVolumeRadius_eq_convexBodyVolumeRoot K x hx,
        sliceVolumeRadius_eq_convexBodyVolumeRoot L y hy]
    _ ≤ convexBodyVolumeRoot ((1 - t) • A + t • B) := hbm
    _ ≤ convexBodyVolumeRoot (verticalSliceBody M z htarget) := hmono
    _ = sliceVolumeRadius M z :=
      (sliceVolumeRadius_eq_convexBodyVolumeRoot M z htarget).symm

/-- Pointwise interpolation inequality for slice radii. -/
theorem weighted_sliceVolumeRadius_le_of_brunnMinkowski
    (hBM : ∀ (t : ℝ) (A B : ConvexBody V),
      0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t A B)
    (K : ConvexBody (ℝ × V)) {t x y : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hx : (verticalSlice (K : Set (ℝ × V)) x).Nonempty)
    (hy : (verticalSlice (K : Set (ℝ × V)) y).Nonempty) :
    (1 - t) * sliceVolumeRadius K x + t * sliceVolumeRadius K y ≤
      sliceVolumeRadius K ((1 - t) * x + t * y) := by
  let A : ConvexBody V := verticalSliceBody K x hx
  let B : ConvexBody V := verticalSliceBody K y hy
  let z : ℝ := (1 - t) * x + t * y
  have hself : (1 - t) • K + t • K = K := by
    apply ConvexBody.ext
    simp only [ConvexBody.coe_add, ConvexBody.coe_smul]
    rw [← K.convex.add_smul (sub_nonneg.mpr ht₁) ht₀]
    simp
  have hsource :
      ((1 - t) • A + t • B : ConvexBody V).carrier ⊆
        verticalSlice (K : Set (ℝ × V)) z := by
    rw [← hself]
    exact weighted_verticalSliceBody_subset K K (t := t) hx hy
  have htarget : (verticalSlice (K : Set (ℝ × V)) z).Nonempty :=
    ((1 - t) • A + t • B).nonempty.mono hsource
  have hmono :
      convexBodyVolumeRoot ((1 - t) • A + t • B) ≤
        convexBodyVolumeRoot (verticalSliceBody K z htarget) :=
    convexBodyVolumeRoot_mono hsource
  have hbm := hBM t A B ht₀ ht₁
  rw [BrunnMinkowskiAt] at hbm
  calc
    (1 - t) * sliceVolumeRadius K x + t * sliceVolumeRadius K y =
        (1 - t) * convexBodyVolumeRoot A + t * convexBodyVolumeRoot B := by
      rw [sliceVolumeRadius_eq_convexBodyVolumeRoot K x hx,
        sliceVolumeRadius_eq_convexBodyVolumeRoot K y hy]
    _ ≤ convexBodyVolumeRoot ((1 - t) • A + t • B) := hbm
    _ ≤ convexBodyVolumeRoot (verticalSliceBody K z htarget) := hmono
    _ = sliceVolumeRadius K z :=
      (sliceVolumeRadius_eq_convexBodyVolumeRoot K z htarget).symm

/-- Lower-dimensional Brunn--Minkowski makes the slice-volume radius a
concave function throughout the projection interval. -/
theorem concaveOn_sliceVolumeRadius
    (hBM : ∀ (t : ℝ) (A B : ConvexBody V),
      0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t A B)
    (K : ConvexBody (ℝ × V)) :
    ConcaveOn ℝ (Icc (sliceLeftEndpoint K) (sliceRightEndpoint K))
      (sliceVolumeRadius K) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxb :
      (verticalSlice (K : Set (ℝ × V)) x).Nonempty :=
    (verticalSlice_nonempty_iff_mem_Icc K x).2 hx
  have hyb :
      (verticalSlice (K : Set (ℝ × V)) y).Nonempty :=
    (verticalSlice_nonempty_iff_mem_Icc K y).2 hy
  have hb1 : b ≤ 1 := by linarith
  have h := weighted_sliceVolumeRadius_le_of_brunnMinkowski hBM K
    (t := b) hb hb1 hxb hyb
  have haeq : a = 1 - b := by linarith
  simpa only [smul_eq_mul, haeq] using h

/-- In particular, the radius profile is continuous on the open projection
interval.  Endpoint continuity is intentionally not claimed. -/
theorem continuousOn_sliceVolumeRadius_Ioo
    (hBM : ∀ (t : ℝ) (A B : ConvexBody V),
      0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t A B)
    (K : ConvexBody (ℝ × V)) :
    ContinuousOn (sliceVolumeRadius K)
      (Ioo (sliceLeftEndpoint K) (sliceRightEndpoint K)) := by
  have hconc := concaveOn_sliceVolumeRadius hBM K
  have hinterior := hconc.continuousOn_interior
  simpa only [interior_Icc] using hinterior

end ZeroOrderBounds.AccuracyImprovement
