import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Normalized spherical measure

This module packages Mathlib's polar-coordinate surface measure as a
probability measure.  Keeping this construction separate makes all later
mean-width statements insensitive to the (dimension-dependent) total surface
area normalization used by `Measure.toSphere`.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

/-- The unit sphere of a real normed space, bundled as a subtype. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  sphere (0 : E) 1

section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The finite surface measure obtained from Euclidean Haar volume by polar
decomposition. -/
def sphereFiniteMeasure : FiniteMeasure (UnitSphere E) :=
  ⟨(volume : Measure E).toSphere, inferInstance⟩

@[simp]
theorem sphereFiniteMeasure_toMeasure :
    ((sphereFiniteMeasure E : FiniteMeasure (UnitSphere E)) :
      Measure (UnitSphere E)) = (volume : Measure E).toSphere :=
  rfl

theorem sphereFiniteMeasure_ne_zero [Nontrivial E] : sphereFiniteMeasure E ≠ 0 := by
  intro h
  have hmeasure :
      ((sphereFiniteMeasure E : FiniteMeasure (UnitSphere E)) :
        Measure (UnitSphere E)) = 0 :=
    congrArg (fun μ : FiniteMeasure (UnitSphere E) ↦ (μ : Measure (UnitSphere E))) h
  exact (Measure.toSphere_ne_zero (volume : Measure E))
    (by simpa [sphereFiniteMeasure] using hmeasure)

/-- Normalized rotational surface measure on the unit sphere. -/
def sphereProbability [Nontrivial E] : ProbabilityMeasure (UnitSphere E) := by
  letI : Nonempty (UnitSphere E) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort
  exact (sphereFiniteMeasure E).normalize

instance [Nontrivial E] : IsProbabilityMeasure
    (sphereProbability E : Measure (UnitSphere E)) := inferInstance

@[simp]
theorem sphereProbability_apply_univ [Nontrivial E] :
    (sphereProbability E : Measure (UnitSphere E)) Set.univ = 1 :=
  measure_univ

theorem sphereProbability_ne_zero [Nontrivial E] :
    (sphereProbability E : Measure (UnitSphere E)) ≠ 0 :=
  IsProbabilityMeasure.ne_zero _

@[simp]
theorem norm_coe_unitSphere (u : UnitSphere E) : ‖(u : E)‖ = 1 := by
  simpa [mem_sphere_zero_iff_norm] using u.property

theorem dist_coe_unitSphere_le_two (u v : UnitSphere E) :
    dist (u : E) (v : E) ≤ 2 := by
  calc
    dist (u : E) (v : E) ≤ dist (u : E) 0 + dist 0 (v : E) :=
      dist_triangle _ _ _
    _ = 2 := by simp [dist_eq_norm]; norm_num

/-- A linear isometry equivalence restricts to a homeomorphism of unit
spheres. -/
def unitSphereEquiv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ₜ UnitSphere F where
  toFun u := ⟨e u, by simpa [mem_sphere_zero_iff_norm] using u.property⟩
  invFun v := ⟨e.symm v, by simpa [mem_sphere_zero_iff_norm] using v.property⟩
  left_inv u := by ext; simp
  right_inv v := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_unitSphereEquiv_apply {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (u : UnitSphere E) :
    ((unitSphereEquiv E e u : UnitSphere F) : F) = e (u : E) :=
  rfl

@[simp]
theorem unitSphereEquiv_symm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereEquiv E e).symm = unitSphereEquiv F e.symm :=
  rfl

/-- Euclidean surface measure is natural under linear isometry equivalences.
This unnormalized statement is useful when a later argument needs to retain the
surface-area constant explicitly. -/
theorem map_toSphere_unitSphereEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (e : E ≃ₗᵢ[ℝ] F) :
    Measure.map (unitSphereEquiv E e) (volume : Measure E).toSphere =
      (volume : Measure F).toSphere := by
  ext s hs
  rw [Measure.map_apply (unitSphereEquiv E e).measurable hs,
    Measure.toSphere_apply' _ ((unitSphereEquiv E e).measurable hs),
    Measure.toSphere_apply' _ hs, e.toLinearEquiv.finrank_eq]
  congr 1
  have hcoe :
      e '' ((fun u : UnitSphere E ↦ (u : E)) ''
        ((unitSphereEquiv E e) ⁻¹' s)) =
        (fun v : UnitSphere F ↦ (v : F)) '' s := by
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨unitSphereEquiv E e u, hu, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      let u : UnitSphere E := (unitSphereEquiv E e).symm v
      refine ⟨(u : E), ⟨u, ?_, rfl⟩, ?_⟩
      · change (unitSphereEquiv E e) u ∈ s
        rw [(unitSphereEquiv E e).apply_symm_apply]
        exact hv
      · simp [u]
  have hsectorImage :
      e '' (Ioo (0 : ℝ) 1 •
        ((fun u : UnitSphere E ↦ (u : E)) ''
          ((unitSphereEquiv E e) ⁻¹' s))) =
        Ioo (0 : ℝ) 1 • ((fun v : UnitSphere F ↦ (v : F)) '' s) := by
    rw [← Set.image2_smul, Set.image_image2_distrib_right]
    · rw [Set.image2_smul, hcoe]
    · intro r x
      exact e.map_smul r x
  have hsectorPreimage :
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((fun v : UnitSphere F ↦ (v : F)) '' s)) =
        Ioo (0 : ℝ) 1 •
          ((fun u : UnitSphere E ↦ (u : E)) ''
            ((unitSphereEquiv E e) ⁻¹' s)) := by
    exact (Set.preimage_eq_iff_eq_image e.bijective).2 hsectorImage.symm
  have hmap := LinearIsometryEquiv.measurePreserving e
  have happly := e.toHomeomorph.toMeasurableEquiv.map_apply
    (μ := (volume : Measure E))
    (Ioo (0 : ℝ) 1 • ((fun v : UnitSphere F ↦ (v : F)) '' s))
  change (Measure.map e (volume : Measure E))
      (Ioo (0 : ℝ) 1 • ((fun v : UnitSphere F ↦ (v : F)) '' s)) =
    (volume : Measure E)
      (e ⁻¹' (Ioo (0 : ℝ) 1 • ((fun v : UnitSphere F ↦ (v : F)) '' s))) at happly
  rw [hmap.map_eq, hsectorPreimage] at happly
  exact happly.symm

/-- Normalized spherical probability is invariant under linear isometry
equivalences. -/
theorem map_sphereProbability_unitSphereEquiv {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [Nontrivial E] [Nontrivial F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Measure.map (unitSphereEquiv E e)
        (sphereProbability E : Measure (UnitSphere E)) =
      (sphereProbability F : Measure (UnitSphere F)) := by
  letI : Nonempty (UnitSphere E) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort
  letI : Nonempty (UnitSphere F) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort
  let μE : FiniteMeasure (UnitSphere E) := sphereFiniteMeasure E
  let μF : FiniteMeasure (UnitSphere F) := sphereFiniteMeasure F
  have hraw : Measure.map (unitSphereEquiv E e) (μE : Measure (UnitSphere E)) =
      (μF : Measure (UnitSphere F)) := by
    simpa [μE, μF, sphereFiniteMeasure] using map_toSphere_unitSphereEquiv E e
  have hmass : μE.mass = μF.mass := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass, ← hraw]
    rw [Measure.map_apply (unitSphereEquiv E e).measurable MeasurableSet.univ,
      preimage_univ]
  ext s hs
  rw [Measure.map_apply (unitSphereEquiv E e).measurable hs]
  change ((μE.normalize : ProbabilityMeasure (UnitSphere E)) :
      Measure (UnitSphere E)) ((unitSphereEquiv E e) ⁻¹' s) =
    ((μF.normalize : ProbabilityMeasure (UnitSphere F)) :
      Measure (UnitSphere F)) s
  rw [μE.toMeasure_normalize_eq_of_nonzero, μF.toMeasure_normalize_eq_of_nonzero]
  · rw [hmass]
    rw [Measure.smul_apply, Measure.smul_apply]
    congr 1
    rw [← hraw, Measure.map_apply (unitSphereEquiv E e).measurable hs]
  · simpa [μF] using sphereFiniteMeasure_ne_zero F
  · simpa [μE] using sphereFiniteMeasure_ne_zero E

/-- A continuous real function on the unit sphere is integrable for normalized
spherical measure. -/
theorem Continuous.integrable_sphereProbability [Nontrivial E]
    {f : UnitSphere E → ℝ} (hf : Continuous f) :
    Integrable f (sphereProbability E : Measure (UnitSphere E)) := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Some point of the sphere is at least the spherical average. -/
theorem exists_integral_le_sphere_value [Nontrivial E]
    {f : UnitSphere E → ℝ} (hf : Continuous f) :
    ∃ u : UnitSphere E,
      (∫ v, f v ∂(sphereProbability E : Measure (UnitSphere E))) ≤ f u := by
  exact exists_integral_le
    (Continuous.integrable_sphereProbability (E := E) hf)

/-- Some point of the sphere is at most the spherical average. -/
theorem exists_sphere_value_le_integral [Nontrivial E]
    {f : UnitSphere E → ℝ} (hf : Continuous f) :
    ∃ u : UnitSphere E,
      f u ≤ ∫ v, f v ∂(sphereProbability E : Measure (UnitSphere E)) := by
  exact exists_le_integral
    (Continuous.integrable_sphereProbability (E := E) hf)

end

end ZeroOrderBounds.AccuracyImprovement
