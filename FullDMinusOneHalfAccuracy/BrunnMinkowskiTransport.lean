import FullDMinusOneHalfAccuracy.BrunnMinkowski
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Transporting Brunn--Minkowski through linear coordinates

The induction proof is most naturally carried out on a product coordinate
space, while the theorem is stated for Euclidean normed spaces.  This file
packages the coordinate change: a continuous linear equivalence sends convex
bodies to convex bodies and commutes exactly with weighted Minkowski sums.
If it preserves volume, it also preserves the homogeneous volume root and
therefore transports `BrunnMinkowskiAt` in both directions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

section BodyImage

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Image of a convex body under a continuous linear equivalence. -/
def continuousLinearEquivImage (e : E ≃L[ℝ] F)
    (K : ConvexBody E) : ConvexBody F where
  carrier := e '' (K : Set E)
  convex' := K.convex.linear_image e.toLinearMap
  isCompact' := K.isCompact.image e.continuous
  nonempty' := K.nonempty.image e

@[simp]
theorem coe_continuousLinearEquivImage (e : E ≃L[ℝ] F)
    (K : ConvexBody E) :
    (continuousLinearEquivImage e K : Set F) = e '' (K : Set E) :=
  rfl

/-- Mapping by an equivalence and then by its inverse recovers the body. -/
@[simp]
theorem continuousLinearEquivImage_symm_image
    (e : E ≃L[ℝ] F) (K : ConvexBody E) :
    continuousLinearEquivImage e.symm (continuousLinearEquivImage e K) = K := by
  apply ConvexBody.ext
  ext x
  simp

@[simp]
theorem continuousLinearEquivImage_image_symm
    (e : E ≃L[ℝ] F) (K : ConvexBody F) :
    continuousLinearEquivImage e (continuousLinearEquivImage e.symm K) = K := by
  apply ConvexBody.ext
  ext x
  simp

/-- Linear coordinate changes commute with scalar dilation. -/
theorem continuousLinearEquivImage_smul
    (e : E ≃L[ℝ] F) (c : ℝ) (K : ConvexBody E) :
    continuousLinearEquivImage e (c • K) =
      c • continuousLinearEquivImage e K := by
  apply ConvexBody.ext
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨e k, ⟨k, hk, rfl⟩, by simp⟩
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨c • k, ⟨k, hk, rfl⟩, by simp⟩

/-- Linear coordinate changes commute with Minkowski addition. -/
theorem continuousLinearEquivImage_add
    (e : E ≃L[ℝ] F) (K L : ConvexBody E) :
    continuousLinearEquivImage e (K + L) =
      continuousLinearEquivImage e K + continuousLinearEquivImage e L := by
  apply ConvexBody.ext
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, l, hl, rfl⟩, rfl⟩
    exact ⟨e k, ⟨k, hk, rfl⟩, e l, ⟨l, hl, rfl⟩, by simp⟩
  · rintro ⟨u, ⟨k, hk, rfl⟩, v, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨k + l, ⟨k, hk, l, hl, rfl⟩, by simp⟩

/-- Exact compatibility with the direct weighted Minkowski expression.  This
form is available even for normed spaces whose norms are not induced by an
inner product (notably the ordinary product norm). -/
theorem continuousLinearEquivImage_weightedSum
    (e : E ≃L[ℝ] F) (t : ℝ) (K L : ConvexBody E) :
    continuousLinearEquivImage e ((1 - t) • K + t • L) =
      (1 - t) • continuousLinearEquivImage e K +
        t • continuousLinearEquivImage e L := by
  rw [continuousLinearEquivImage_add,
    continuousLinearEquivImage_smul,
    continuousLinearEquivImage_smul]

end BodyImage

section Measure

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- A measure-preserving linear equivalence preserves the volume of every
convex body.  The statement is measure-generic so its measurable-space
instances are fixed by the `MeasurePreserving` witness; this is important for
the `WithLp` specialization. -/
theorem measure_continuousLinearEquivImage_eq
    (e : E ≃L[ℝ] F)
    (muE : Measure E) (muF : Measure F)
    (hmp : MeasurePreserving e muE muF)
    (K : ConvexBody E) :
    muF (continuousLinearEquivImage e K : Set F) =
      muE (K : Set E) := by
  have hpre := hmp.measure_preimage
    (continuousLinearEquivImage e K).isCompact.measurableSet.nullMeasurableSet
  simpa only [coe_continuousLinearEquivImage,
    e.injective.preimage_image] using hpre.symm

end Measure

section VolumeRoot

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- In inner-product spaces the direct compatibility lemma is exactly the
repository's `weightedMinkowski` operation. -/
theorem continuousLinearEquivImage_weightedMinkowski
    (e : E ≃L[ℝ] F) (t : ℝ) (K L : ConvexBody E) :
    continuousLinearEquivImage e (weightedMinkowski t K L) =
      weightedMinkowski t (continuousLinearEquivImage e K)
        (continuousLinearEquivImage e L) := by
  simpa only [weightedMinkowski] using
    continuousLinearEquivImage_weightedSum e t K L

theorem convexBodyVolumeReal_continuousLinearEquivImage_eq
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    (K : ConvexBody E) :
    convexBodyVolumeReal (continuousLinearEquivImage e K) =
      convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal,
    measure_continuousLinearEquivImage_eq e volume volume hmp K]

/-- Volume root is invariant under a volume-preserving linear coordinate
equivalence. -/
theorem convexBodyVolumeRoot_continuousLinearEquivImage_eq
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    (K : ConvexBody E) :
    convexBodyVolumeRoot (continuousLinearEquivImage e K) =
      convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_continuousLinearEquivImage_eq e hmp K,
    ← e.toLinearEquiv.finrank_eq]

/-- `BrunnMinkowskiAt` is invariant under a volume-preserving continuous
linear equivalence.  The biconditional provides both transport directions. -/
theorem brunnMinkowskiAt_continuousLinearEquivImage_iff
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    (t : ℝ) (K L : ConvexBody E) :
    BrunnMinkowskiAt t (continuousLinearEquivImage e K)
        (continuousLinearEquivImage e L) ↔
      BrunnMinkowskiAt t K L := by
  rw [BrunnMinkowskiAt, BrunnMinkowskiAt,
    ← continuousLinearEquivImage_weightedMinkowski e t K L,
    convexBodyVolumeRoot_continuousLinearEquivImage_eq e hmp,
    convexBodyVolumeRoot_continuousLinearEquivImage_eq e hmp,
    convexBodyVolumeRoot_continuousLinearEquivImage_eq e hmp]

theorem BrunnMinkowskiAt.map_continuousLinearEquiv
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    {t : ℝ} {K L : ConvexBody E}
    (h : BrunnMinkowskiAt t K L) :
    BrunnMinkowskiAt t (continuousLinearEquivImage e K)
      (continuousLinearEquivImage e L) :=
  (brunnMinkowskiAt_continuousLinearEquivImage_iff e hmp t K L).2 h

theorem BrunnMinkowskiAt.of_map_continuousLinearEquiv
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    {t : ℝ} {K L : ConvexBody E}
    (h : BrunnMinkowskiAt t (continuousLinearEquivImage e K)
      (continuousLinearEquivImage e L)) :
    BrunnMinkowskiAt t K L :=
  (brunnMinkowskiAt_continuousLinearEquivImage_iff e hmp t K L).1 h

end VolumeRoot

/-! ## The L2 product coordinate equivalence -/

section WithLpProduct

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Forget the L2 product norm on a convex body, mapping it to the ordinary
product model used by the slicing theorem. -/
def ofLpConvexBody (K : ConvexBody (WithLp 2 (U × V))) :
    ConvexBody (U × V) :=
  continuousLinearEquivImage
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V) K

/-- Equip a body in the ordinary product model with the L2 product norm. -/
def toLpConvexBody (K : ConvexBody (U × V)) :
    ConvexBody (WithLp 2 (U × V)) :=
  continuousLinearEquivImage
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm K

@[simp]
theorem toLpConvexBody_ofLpConvexBody
    (K : ConvexBody (WithLp 2 (U × V))) :
    toLpConvexBody (ofLpConvexBody K) = K :=
  continuousLinearEquivImage_symm_image
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V) K

@[simp]
theorem ofLpConvexBody_toLpConvexBody
    (K : ConvexBody (U × V)) :
    ofLpConvexBody (toLpConvexBody K) = K :=
  continuousLinearEquivImage_image_symm
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V) K

/-- `ofLp` preserves the exact volume normalization used by product
slicing. -/
theorem volume_ofLpConvexBody (K : ConvexBody (WithLp 2 (U × V))) :
    volume (ofLpConvexBody K : Set (U × V)) =
      volume (K : Set (WithLp 2 (U × V))) := by
  exact measure_continuousLinearEquivImage_eq
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V) volume volume
    (WithLp.volume_preserving_ofLp U V) K

/-- `toLp` preserves product volume in the reverse direction. -/
theorem volume_toLpConvexBody (K : ConvexBody (U × V)) :
    volume (toLpConvexBody K : Set (WithLp 2 (U × V))) =
      volume (K : Set (U × V)) := by
  exact measure_continuousLinearEquivImage_eq
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm volume volume
    (WithLp.volume_preserving_toLp U V) K

theorem ofLpConvexBody_weightedSum
    (t : ℝ) (K L : ConvexBody (WithLp 2 (U × V))) :
    ofLpConvexBody ((1 - t) • K + t • L) =
      (1 - t) • ofLpConvexBody K + t • ofLpConvexBody L :=
  continuousLinearEquivImage_weightedSum
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V) t K L

theorem toLpConvexBody_weightedSum
    (t : ℝ) (K L : ConvexBody (U × V)) :
    toLpConvexBody ((1 - t) • K + t • L) =
      (1 - t) • toLpConvexBody K + t • toLpConvexBody L :=
  continuousLinearEquivImage_weightedSum
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm t K L

/-- The volume root of the L2 realization is exactly the product volume to
the reciprocal product dimension. -/
theorem convexBodyVolumeRoot_toLpConvexBody
    (K : ConvexBody (U × V)) :
    convexBodyVolumeRoot (toLpConvexBody K) =
      (volume (K : Set (U × V))).toReal ^
        ((Module.finrank ℝ (U × V) : ℝ)⁻¹) := by
  rw [convexBodyVolumeRoot, convexBodyVolumeReal,
    volume_toLpConvexBody,
    (WithLp.prodContinuousLinearEquiv 2 ℝ U V).toLinearEquiv.finrank_eq]

/-- Exact audit boundary between Brunn--Minkowski on the L2 product and the
corresponding real-volume-root inequality in the ordinary product model. -/
theorem brunnMinkowskiAt_toLpConvexBody_iff
    (t : ℝ) (K L : ConvexBody (U × V)) :
    BrunnMinkowskiAt t (toLpConvexBody K) (toLpConvexBody L) ↔
      (1 - t) *
          (volume (K : Set (U × V))).toReal ^
            ((Module.finrank ℝ (U × V) : ℝ)⁻¹) +
        t *
          (volume (L : Set (U × V))).toReal ^
            ((Module.finrank ℝ (U × V) : ℝ)⁻¹) ≤
        (volume (((1 - t) • K + t • L : ConvexBody (U × V)) :
          Set (U × V))).toReal ^
            ((Module.finrank ℝ (U × V) : ℝ)⁻¹) := by
  rw [BrunnMinkowskiAt,
    weightedMinkowski,
    ← toLpConvexBody_weightedSum t K L,
    convexBodyVolumeRoot_toLpConvexBody,
    convexBodyVolumeRoot_toLpConvexBody,
    convexBodyVolumeRoot_toLpConvexBody]

/-- In the equal-volume case, the product-volume comparison supplied by the
slicing theorem immediately yields Brunn--Minkowski on the L2 realization. -/
theorem brunnMinkowskiAt_toLpConvexBody_of_equal_volume
    (t : ℝ) (K L : ConvexBody (U × V))
    (hEq : (volume (K : Set (U × V))).toReal =
      (volume (L : Set (U × V))).toReal)
    (hvol : (volume (K : Set (U × V))).toReal ≤
      (volume (((1 - t) • K + t • L : ConvexBody (U × V)) :
        Set (U × V))).toReal) :
    BrunnMinkowskiAt t (toLpConvexBody K) (toLpConvexBody L) := by
  apply (brunnMinkowskiAt_toLpConvexBody_iff t K L).2
  let p : ℝ := (Module.finrank ℝ (U × V) : ℝ)⁻¹
  have hp : 0 ≤ p := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hroot := Real.rpow_le_rpow ENNReal.toReal_nonneg hvol hp
  change (1 - t) *
      (volume (K : Set (U × V))).toReal ^ p +
    t * (volume (L : Set (U × V))).toReal ^ p ≤
      (volume (((1 - t) • K + t • L : ConvexBody (U × V)) :
        Set (U × V))).toReal ^ p
  rw [← hEq]
  nlinarith

end WithLpProduct

end ZeroOrderBounds.AccuracyImprovement
