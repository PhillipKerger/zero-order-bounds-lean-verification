import FullDMinusOneHalfAccuracy.BrunnMinkowski
import FullDMinusOneHalfAccuracy.MinkowskiWidth
import FullDMinusOneHalfAccuracy.SphericalProjection

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Intrinsic affine coordinates for row bodies

An oracle row body generally lies in a proper affine subspace.  Urysohn's
inequality, however, is most conveniently stated for a full-dimensional
convex body in a vector space.  This module translates an `IntrinsicBody` by
a point of its affine hull and pulls it back to the hull's direction space.

The construction preserves its intrinsic volume and its full directional
widths exactly.  These identities form the audit boundary between the generic
full-dimensional Urysohn theorem and the row-body statement used by the
optimization proof.
-/

noncomputable section

open Metric MeasureTheory Set

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace IntrinsicCoordinates

/-- A canonical point of the affine hull, chosen from the body itself. -/
def basepoint (P : IntrinsicBody E) : P.hull :=
  ⟨P.nonempty.some, subset_affineSpan ℝ P.carrier P.nonempty.some_mem⟩

instance hullNonempty (P : IntrinsicBody E) : Nonempty P.hull :=
  ⟨basepoint P⟩

/-- The body regarded as a subset of its affine hull. -/
def hullCarrier (P : IntrinsicBody E) : Set P.hull :=
  Subtype.val ⁻¹' P.carrier

theorem coe_image_hullCarrier (P : IntrinsicBody E) :
    Subtype.val '' hullCarrier P = P.carrier := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, P.carrier_subset_hull hx⟩, hx, rfl⟩

theorem hullCarrier_isCompact (P : IntrinsicBody E) :
    IsCompact (hullCarrier P) := by
  rw [Subtype.isCompact_iff, coe_image_hullCarrier]
  exact P.isCompact

/-- Translation by the chosen point identifies the hull direction with the
affine hull isometrically. -/
def coordinateIsometry (P : IntrinsicBody E) :
    P.directionSpan ≃ᵢ P.hull := by
  change P.hull.direction ≃ᵢ P.hull
  exact IsometryEquiv.vaddConst (basepoint P)

@[simp]
theorem coe_coordinateIsometry_apply (P : IntrinsicBody E)
    (v : P.directionSpan) :
    ((coordinateIsometry P v : P.hull) : E) =
      (v : E) + (basepoint P : E) := by
  change (((IsometryEquiv.vaddConst (basepoint P)) v : P.hull) : E) = _
  rfl

/-- The body pulled back to the vector space of directions of its affine
hull. -/
def coordinateCarrier (P : IntrinsicBody E) : Set P.directionSpan :=
  coordinateIsometry P ⁻¹' hullCarrier P

@[simp]
theorem mem_coordinateCarrier (P : IntrinsicBody E)
    (v : P.directionSpan) :
    v ∈ coordinateCarrier P ↔
      (v : E) + (basepoint P : E) ∈ P.carrier := by
  change ((coordinateIsometry P v : P.hull) : E) ∈ P.carrier ↔ _
  rw [coe_coordinateIsometry_apply]

theorem coordinateCarrier_nonempty (P : IntrinsicBody E) :
    (coordinateCarrier P).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_coordinateCarrier]
  simpa [basepoint] using P.nonempty.some_mem

theorem coordinateCarrier_isCompact (P : IntrinsicBody E) :
    IsCompact (coordinateCarrier P) := by
  exact (coordinateIsometry P).toHomeomorph.isCompact_preimage.mpr
    (hullCarrier_isCompact P)

theorem coordinateCarrier_convex (P : IntrinsicBody E) :
    Convex ℝ (coordinateCarrier P) := by
  intro x hx y hy a b ha hb hab
  rw [mem_coordinateCarrier] at hx hy ⊢
  convert P.convex hx hy ha hb hab using 1
  simp only [Submodule.coe_add, Submodule.coe_smul]
  have hbEq : b = 1 - a := by linarith
  rw [hbEq]
  module

/-- The full-dimensional convex body in intrinsic coordinates. -/
def coordinateBody (P : IntrinsicBody E) : ConvexBody P.directionSpan where
  carrier := coordinateCarrier P
  convex' := coordinateCarrier_convex P
  isCompact' := coordinateCarrier_isCompact P
  nonempty' := coordinateCarrier_nonempty P

@[simp]
theorem coe_coordinateBody (P : IntrinsicBody E) :
    (coordinateBody P : Set P.directionSpan) = coordinateCarrier P :=
  rfl

/-- Coercing the intrinsic-coordinate body back to the ambient vector space
gives the original body translated by the negative basepoint. -/
theorem coe_image_coordinateCarrier (P : IntrinsicBody E) :
    ((fun v : P.directionSpan => (v : E)) '' coordinateCarrier P) =
      (fun x : E => -(basepoint P : E) + x) '' P.carrier := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_coordinateCarrier] at hv
    refine ⟨(basepoint P : E) + (v : E), ?_, by simp⟩
    simpa [add_comm] using hv
  · rintro ⟨x, hx, rfl⟩
    have hxHull : x ∈ P.hull := P.carrier_subset_hull hx
    have hvMem : x - (basepoint P : E) ∈ P.directionSpan :=
      P.hull.vsub_mem_direction hxHull (basepoint P).property
    let v : P.directionSpan := ⟨x - (basepoint P : E), hvMem⟩
    refine ⟨v, ?_, ?_⟩
    · rw [mem_coordinateCarrier]
      simpa [v] using hx
    · change x - (basepoint P : E) = -(basepoint P : E) + x
      abel

/-- Directional widths are unchanged by passage to intrinsic coordinates. -/
theorem directionalWidth_coordinateBody (P : IntrinsicBody E)
    (theta : P.directionSpan) :
    directionalWidth (coordinateBody P : Set P.directionSpan) theta =
      P.directionalWidth (theta : E) := by
  have hsubtype := directionalWidth_image_eq_of_inner_sub_eq_cross
    (coordinateBody P).isCompact (coordinateBody P).nonempty
    (fun v : P.directionSpan => (v : E))
    (by fun_prop) (theta := (theta : E)) (phi := theta) (by
      intro x hx y hy
      rfl)
  rw [coe_coordinateBody, coe_image_coordinateCarrier,
    directionalWidth_translate_image P.isCompact P.nonempty
      (-(basepoint P : E)) (theta : E)] at hsubtype
  exact hsubtype.symm

/-- The volume of the coordinate body is the body's intrinsic Hausdorff
volume. -/
theorem volume_coordinateBody (P : IntrinsicBody E) (hdim : P.dim ≠ 0) :
    volume (coordinateBody P : Set P.directionSpan) = P.volume := by
  have hmeasure :=
    (EuclideanGeometry.measurePreserving_vaddConst (basepoint P)).measure_preimage_equiv
      (f := (IsometryEquiv.vaddConst (basepoint P)).toHomeomorph.toMeasurableEquiv)
      (hullCarrier P)
  calc
    volume (coordinateBody P : Set P.directionSpan) =
        μHE[P.dim] (hullCarrier P) := by
      change volume (coordinateCarrier P) = _
      change volume
          ((IsometryEquiv.vaddConst (basepoint P)) ⁻¹' hullCarrier P) =
        μHE[Module.finrank ℝ P.hull.direction] (hullCarrier P)
      exact hmeasure
    _ = μHE[P.dim] (Subtype.val '' hullCarrier P) :=
      (P.hull.euclideanHausdorffMeasure_coe_image P.dim (hullCarrier P)).symm
    _ = μHE[P.dim] P.carrier := by rw [coe_image_hullCarrier]
    _ = intrinsicVolume P.carrier := by
      rw [intrinsicVolume_of_affineDim_ne_zero hdim]
      rfl

/-- Real volume is likewise preserved. -/
theorem volumeReal_coordinateBody (P : IntrinsicBody E) (hdim : P.dim ≠ 0) :
    convexBodyVolumeReal (coordinateBody P) = P.volumeReal := by
  rw [convexBodyVolumeReal, IntrinsicBody.volumeReal,
    intrinsicVolumeReal, volume_coordinateBody P hdim]
  rfl

/-- Intrinsic mean width is exactly the spherical mean width of the coordinate
body. -/
theorem sphericalMeanWidth_coordinateBody (P : IntrinsicBody E)
    [Nontrivial P.directionSpan] :
    convexBodySphericalMeanWidth (coordinateBody P) =
      intrinsicMeanWidth P P.directionSpan := by
  rw [convexBodySphericalMeanWidth, intrinsicMeanWidth]
  apply integral_congr_ae
  filter_upwards with u
  exact directionalWidth_coordinateBody P u

end IntrinsicCoordinates

end ZeroOrderBounds.AccuracyImprovement
