import FullDMinusOneHalfAccuracy.DirectionalWidth
import FullDMinusOneHalfAccuracy.PolarFactorization
import FullDMinusOneHalfAccuracy.SphereMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Spherical projection and averaging

This file contains the dimension-loss calculation used when an intrinsic
directional-width estimate is viewed from an ambient Euclidean sphere.  The
basic random variable is the norm of the orthogonal projection of an ambient
unit vector onto a fixed subspace.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Metric Set

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The radial norm of the projection of an ambient unit vector onto `L`. -/
def projectedRadialNorm (L : Submodule ℝ E) (u : UnitSphere E) : ℝ :=
  ‖L.starProjection (u : E)‖

theorem projectedRadialNorm_nonneg (L : Submodule ℝ E) (u : UnitSphere E) :
    0 ≤ projectedRadialNorm L u :=
  norm_nonneg _

theorem projectedRadialNorm_le_one (L : Submodule ℝ E) (u : UnitSphere E) :
    projectedRadialNorm L u ≤ 1 := by
  simpa [projectedRadialNorm, norm_coe_unitSphere] using
    L.norm_starProjection_apply_le (u : E)

theorem projectedRadialNorm_mem_Icc (L : Submodule ℝ E) (u : UnitSphere E) :
    projectedRadialNorm L u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨projectedRadialNorm_nonneg L u, projectedRadialNorm_le_one L u⟩

theorem projectedRadialNorm_sq_le (L : Submodule ℝ E) (u : UnitSphere E) :
    projectedRadialNorm L u ^ 2 ≤ projectedRadialNorm L u := by
  rcases projectedRadialNorm_mem_Icc L u with ⟨h₀, h₁⟩
  nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]

theorem continuous_projectedRadialNorm (L : Submodule ℝ E) :
    Continuous (projectedRadialNorm L) := by
  exact (L.starProjection.continuous.comp continuous_subtype_val).norm

theorem measurable_projectedRadialNorm (L : Submodule ℝ E) :
    Measurable (projectedRadialNorm L) :=
  (continuous_projectedRadialNorm L).measurable

theorem integrable_projectedRadialNorm [Nontrivial E] (L : Submodule ℝ E) :
    Integrable (projectedRadialNorm L)
      (sphereProbability E : Measure (UnitSphere E)) :=
  ZeroOrderBounds.AccuracyImprovement.Continuous.integrable_sphereProbability
    (E := E) (continuous_projectedRadialNorm L)

theorem integrable_projectedRadialNorm_sq [Nontrivial E] (L : Submodule ℝ E) :
    Integrable (fun u : UnitSphere E ↦ projectedRadialNorm L u ^ 2)
      (sphereProbability E : Measure (UnitSphere E)) := by
  apply ZeroOrderBounds.AccuracyImprovement.Continuous.integrable_sphereProbability (E := E)
  exact (continuous_projectedRadialNorm L).pow 2

/-- On the unit interval, the first radial moment dominates the second. -/
theorem integral_projectedRadialNorm_sq_le_integral [Nontrivial E]
    (L : Submodule ℝ E) :
    (∫ u, projectedRadialNorm L u ^ 2
        ∂(sphereProbability E : Measure (UnitSphere E))) ≤
      ∫ u, projectedRadialNorm L u
        ∂(sphereProbability E : Measure (UnitSphere E)) := by
  exact integral_mono
    (integrable_projectedRadialNorm_sq L)
    (integrable_projectedRadialNorm L)
    (projectedRadialNorm_sq_le L)

/-- The second moment of the coordinate in a fixed ambient direction. -/
def sphereCoordinateSecondMoment [Nontrivial E] (v : E) : ℝ :=
  ∫ u : UnitSphere E, inner ℝ (u : E) v ^ 2
    ∂(sphereProbability E : Measure (UnitSphere E))

theorem integrable_sphereCoordinate_sq [Nontrivial E] (v : E) :
    Integrable (fun u : UnitSphere E ↦ inner ℝ (u : E) v ^ 2)
      (sphereProbability E : Measure (UnitSphere E)) := by
  apply ZeroOrderBounds.AccuracyImprovement.Continuous.integrable_sphereProbability (E := E)
  fun_prop

/-- Rotational invariance makes the coordinate second moment depend only on
the norm of the direction. -/
theorem sphereCoordinateSecondMoment_eq_of_norm_eq [Nontrivial E]
    {v w : E} (hvw : ‖v‖ = ‖w‖) :
    sphereCoordinateSecondMoment (E := E) v =
      sphereCoordinateSecondMoment (E := E) w := by
  let e : E ≃ₗᵢ[ℝ] E := ((ℝ ∙ (v - w))ᗮ).reflection
  have he : e v = w := Submodule.reflection_sub hvw
  have hpres : MeasurePreserving (unitSphereEquiv E e)
      (sphereProbability E : Measure (UnitSphere E))
      (sphereProbability E : Measure (UnitSphere E)) :=
    ⟨(unitSphereEquiv E e).measurable,
      map_sphereProbability_unitSphereEquiv E e⟩
  calc
    sphereCoordinateSecondMoment (E := E) v =
        ∫ u : UnitSphere E,
          inner ℝ ((unitSphereEquiv E e u : UnitSphere E) : E) w ^ 2
            ∂(sphereProbability E : Measure (UnitSphere E)) := by
          apply integral_congr_ae
          filter_upwards with u
          change inner ℝ (u : E) v ^ 2 = inner ℝ (e (u : E)) w ^ 2
          rw [← he, e.inner_map_map]
    _ = sphereCoordinateSecondMoment (E := E) w := by
      exact hpres.integral_comp (unitSphereEquiv E e).measurableEmbedding
        (fun u : UnitSphere E ↦ inner ℝ (u : E) w ^ 2)

/-- Every unit coordinate of normalized spherical measure has second moment
`1 / dim E`. -/
theorem sphereCoordinateSecondMoment_of_norm_eq_one [Nontrivial E]
    {v : E} (hv : ‖v‖ = 1) :
    sphereCoordinateSecondMoment (E := E) v =
      (Module.finrank ℝ E : ℝ)⁻¹ := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  let b : OrthonormalBasis (Fin n) ℝ E := stdOrthonormalBasis ℝ E
  let i₀ : Fin n := ⟨0, hn⟩
  have hb₀ : ‖b i₀‖ = 1 := b.norm_eq_one i₀
  have heq (i : Fin n) :
      sphereCoordinateSecondMoment (E := E) (b i) =
        sphereCoordinateSecondMoment (E := E) (b i₀) :=
    sphereCoordinateSecondMoment_eq_of_norm_eq
      ((b.norm_eq_one i).trans hb₀.symm)
  have hsum :
      ∑ i : Fin n, sphereCoordinateSecondMoment (E := E) (b i) = 1 := by
    calc
      ∑ i : Fin n, sphereCoordinateSecondMoment (E := E) (b i) =
          ∫ u : UnitSphere E, ∑ i : Fin n, inner ℝ (u : E) (b i) ^ 2
            ∂(sphereProbability E : Measure (UnitSphere E)) := by
              simp only [sphereCoordinateSecondMoment]
              exact (integral_finsetSum Finset.univ fun i _ ↦
                integrable_sphereCoordinate_sq (E := E) (b i)).symm
      _ = ∫ _u : UnitSphere E, (1 : ℝ)
            ∂(sphereProbability E : Measure (UnitSphere E)) := by
              apply integral_congr_ae
              filter_upwards with u
              rw [b.sum_sq_inner_left, norm_coe_unitSphere, one_pow]
      _ = 1 := by simp
  have hbase :
      sphereCoordinateSecondMoment (E := E) (b i₀) = (n : ℝ)⁻¹ := by
    have hmul : (n : ℝ) * sphereCoordinateSecondMoment (E := E) (b i₀) = 1 := by
      simpa [heq, nsmul_eq_mul] using hsum
    exact eq_inv_of_mul_eq_one_right hmul
  calc
    sphereCoordinateSecondMoment (E := E) v =
        sphereCoordinateSecondMoment (E := E) (b i₀) :=
      sphereCoordinateSecondMoment_eq_of_norm_eq (hv.trans hb₀.symm)
    _ = (n : ℝ)⁻¹ := hbase
    _ = (Module.finrank ℝ E : ℝ)⁻¹ := rfl

/-- Parseval's identity for the squared norm of an orthogonal projection,
written in an orthonormal basis of the target subspace. -/
theorem projectedRadialNorm_sq_eq_sum_inner (L : Submodule ℝ E)
    (u : UnitSphere E) :
    projectedRadialNorm L u ^ 2 =
      ∑ i : Fin (Module.finrank ℝ L),
        inner ℝ (((stdOrthonormalBasis ℝ L) i : L) : E) (u : E) ^ 2 := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L :=
    stdOrthonormalBasis ℝ L
  change ‖L.starProjection (u : E)‖ ^ 2 =
    ∑ i, inner ℝ ((b i : L) : E) (u : E) ^ 2
  rw [L.starProjection_apply, ← Submodule.coe_norm]
  rw [← b.sum_sq_inner_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Exact second radial moment: an orthogonal projection onto a `k`-plane in
an `m`-dimensional space has mean squared norm `k/m` on the unit sphere. -/
theorem integral_projectedRadialNorm_sq [Nontrivial E]
    (L : Submodule ℝ E) :
    (∫ u : UnitSphere E, projectedRadialNorm L u ^ 2
        ∂(sphereProbability E : Measure (UnitSphere E))) =
      (Module.finrank ℝ L : ℝ) / (Module.finrank ℝ E : ℝ) := by
  rw [show (∫ u : UnitSphere E, projectedRadialNorm L u ^ 2
      ∂(sphereProbability E : Measure (UnitSphere E))) =
      ∫ u : UnitSphere E,
        ∑ i : Fin (Module.finrank ℝ L),
          inner ℝ (((stdOrthonormalBasis ℝ L) i : L) : E) (u : E) ^ 2
        ∂(sphereProbability E : Measure (UnitSphere E)) by
      apply integral_congr_ae
      filter_upwards with u
      exact projectedRadialNorm_sq_eq_sum_inner L u]
  rw [integral_finsetSum]
  · have hunit (i : Fin (Module.finrank ℝ L)) :
        ‖(((stdOrthonormalBasis ℝ L) i : L) : E)‖ = 1 := by
      rw [← Submodule.coe_norm]
      exact (stdOrthonormalBasis ℝ L).norm_eq_one i
    have hmoment (i : Fin (Module.finrank ℝ L)) :
        (∫ u : UnitSphere E,
          inner ℝ (((stdOrthonormalBasis ℝ L) i : L) : E) (u : E) ^ 2
            ∂(sphereProbability E : Measure (UnitSphere E))) =
          (Module.finrank ℝ E : ℝ)⁻¹ := by
      rw [show (∫ u : UnitSphere E,
          inner ℝ (((stdOrthonormalBasis ℝ L) i : L) : E) (u : E) ^ 2
            ∂(sphereProbability E : Measure (UnitSphere E))) =
          sphereCoordinateSecondMoment (E := E)
            (((stdOrthonormalBasis ℝ L) i : L) : E) by
        apply integral_congr_ae
        filter_upwards with u
        exact congrArg (fun x : ℝ ↦ x ^ 2) (real_inner_comm _ _)]
      exact sphereCoordinateSecondMoment_of_norm_eq_one (hunit i)
    rw [Finset.sum_congr rfl fun i _ ↦ hmoment i]
    simp [div_eq_mul_inv]
  · intro i hi
    have h := integrable_sphereCoordinate_sq (E := E)
      (((stdOrthonormalBasis ℝ L) i : L) : E)
    apply h.congr
    filter_upwards with u
    exact congrArg (fun x : ℝ ↦ x ^ 2) (real_inner_comm _ _)

/-- The paper's radial estimate `E R ≥ E R² = k/m`. -/
theorem finrank_div_finrank_le_integral_projectedRadialNorm [Nontrivial E]
    (L : Submodule ℝ E) :
    (Module.finrank ℝ L : ℝ) / (Module.finrank ℝ E : ℝ) ≤
      ∫ u : UnitSphere E, projectedRadialNorm L u
        ∂(sphereProbability E : Measure (UnitSphere E)) := by
  rw [← integral_projectedRadialNorm_sq L]
  exact integral_projectedRadialNorm_sq_le_integral L

/-- In particular, a subspace occupying at least half the ambient dimension
loses at most a factor two in the mean projected radius. -/
theorem one_half_le_integral_projectedRadialNorm [Nontrivial E]
    (L : Submodule ℝ E)
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ L) :
    (1 : ℝ) / 2 ≤
      ∫ u : UnitSphere E, projectedRadialNorm L u
        ∂(sphereProbability E : Measure (UnitSphere E)) := by
  apply le_trans ?_ (finrank_div_finrank_le_integral_projectedRadialNorm L)
  have hE : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hE]
  norm_num
  exact_mod_cast (by simpa [mul_comm] using hdim)

/-- A unit vector in a nonzero subspace, used only on the zero-projection
fiber when making normalization total. -/
def fallbackUnitSphere (L : Submodule ℝ E) [Nontrivial L] : UnitSphere L :=
  Classical.choice
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort

/-- Normalize the orthogonal projection.  At the zero projection (a spherical
null set in the applications), choose an arbitrary unit vector of `L`. -/
def projectedDirection (L : Submodule ℝ E) [Nontrivial L]
    (u : UnitSphere E) : UnitSphere L := by
  classical
  by_cases h : projectedRadialNorm L u = 0
  · exact fallbackUnitSphere L
  · let p : L := ⟨L.starProjection (u : E), by simp⟩
    refine ⟨(projectedRadialNorm L u)⁻¹ • p, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Submodule.coe_norm,
      show ‖(p : E)‖ = projectedRadialNorm L u by rfl]
    rw [Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (projectedRadialNorm_nonneg L u), inv_mul_cancel₀ h]

theorem norm_coe_projectedDirection (L : Submodule ℝ E) [Nontrivial L]
    (u : UnitSphere E) : ‖((projectedDirection L u : L) : E)‖ = 1 := by
  calc
    ‖((projectedDirection L u : L) : E)‖ = ‖(projectedDirection L u : L)‖ :=
      (Submodule.coe_norm _).symm
    _ = 1 := norm_coe_unitSphere (E := L) (projectedDirection L u)

theorem coe_projectedDirection_of_ne (L : Submodule ℝ E) [Nontrivial L]
    (u : UnitSphere E) (h : projectedRadialNorm L u ≠ 0) :
    (((projectedDirection L u : L) : E)) =
      (projectedRadialNorm L u)⁻¹ • L.starProjection (u : E) := by
  simp [projectedDirection, h]

/-- Radial-direction decomposition of an orthogonal projection. -/
theorem projectedRadialNorm_smul_projectedDirection (L : Submodule ℝ E)
    [Nontrivial L] (u : UnitSphere E) :
    projectedRadialNorm L u • (((projectedDirection L u : L) : E)) =
      L.starProjection (u : E) := by
  classical
  by_cases h : projectedRadialNorm L u = 0
  · have hp : L.starProjection (u : E) = 0 := norm_eq_zero.mp h
    simp [h, hp]
  · rw [coe_projectedDirection_of_ne L u h]
    rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Intrinsic width as a function on the unit sphere of a subspace. -/
def intrinsicSphereWidth (P : IntrinsicBody E) (L : Submodule ℝ E)
    (v : UnitSphere L) : ℝ :=
  P.directionalWidth ((v : L) : E)

theorem continuous_intrinsicSphereWidth (P : IntrinsicBody E)
    (L : Submodule ℝ E) : Continuous (intrinsicSphereWidth P L) := by
  exact P.continuous_directionalWidth.comp
    (L.subtypeL.continuous.comp continuous_subtype_val)

theorem integrable_intrinsicSphereWidth (P : IntrinsicBody E)
    (L : Submodule ℝ E) [Nontrivial L] :
    Integrable (intrinsicSphereWidth P L)
      (sphereProbability L : Measure (UnitSphere L)) :=
  ZeroOrderBounds.AccuracyImprovement.Continuous.integrable_sphereProbability
    (E := L) (continuous_intrinsicSphereWidth P L)

/-- Mean full width on an ambient Euclidean sphere. -/
def ambientMeanWidth [Nontrivial E] (P : IntrinsicBody E) : ℝ :=
  ∫ u : UnitSphere E, P.directionalWidth (u : E)
    ∂(sphereProbability E : Measure (UnitSphere E))

/-- Mean full width inside a specified intrinsic subspace. -/
def intrinsicMeanWidth (P : IntrinsicBody E) (L : Submodule ℝ E)
    [Nontrivial L] : ℝ :=
  ∫ v : UnitSphere L, intrinsicSphereWidth P L v
    ∂(sphereProbability L : Measure (UnitSphere L))

theorem integrable_ambient_directionalWidth [Nontrivial E] (P : IntrinsicBody E) :
    Integrable (fun u : UnitSphere E ↦ P.directionalWidth (u : E))
      (sphereProbability E : Measure (UnitSphere E)) := by
  apply ZeroOrderBounds.AccuracyImprovement.Continuous.integrable_sphereProbability (E := E)
  exact P.continuous_directionalWidth.comp continuous_subtype_val

/-- Width is the projected radial norm times width in the normalized projected
direction.  This is the pointwise identity behind spherical disintegration. -/
theorem directionalWidth_eq_projectedRadialNorm_mul
    (P : IntrinsicBody E) (L : Submodule ℝ E) [Nontrivial L]
    (hspan : P.directionSpan = L) (u : UnitSphere E) :
    P.directionalWidth (u : E) =
      projectedRadialNorm L u * intrinsicSphereWidth P L (projectedDirection L u) := by
  rw [← P.directionalWidth_starProjection_directionSpan (u : E), hspan]
  rw [← projectedRadialNorm_smul_projectedDirection L u]
  rw [P.directionalWidth_smul_of_nonneg _ (projectedRadialNorm_nonneg L u)]
  rfl

theorem intrinsicMeanWidth_nonneg (P : IntrinsicBody E)
    (L : Submodule ℝ E) [Nontrivial L] :
    0 ≤ intrinsicMeanWidth P L := by
  apply integral_nonneg
  intro v
  exact P.directionalWidth_nonneg _

@[simp]
theorem finrank_directionSpan_eq_dim (P : IntrinsicBody E) :
    Module.finrank ℝ P.directionSpan = P.dim :=
  rfl

theorem integral_projectedRadialNorm_nonneg [Nontrivial E]
    (L : Submodule ℝ E) :
    0 ≤ ∫ u : UnitSphere E, projectedRadialNorm L u
      ∂(sphereProbability E : Measure (UnitSphere E)) := by
  apply integral_nonneg
  exact projectedRadialNorm_nonneg L

/-- Exact normalized spherical factorization for a body's width. -/
theorem ambientMeanWidth_eq_projectedRadial_mul_intrinsicMeanWidth
    [Nontrivial E] (P : IntrinsicBody E) (L : Submodule ℝ E)
    [Nontrivial L] (hspan : P.directionSpan = L) :
    ambientMeanWidth P =
      (∫ u : UnitSphere E, projectedRadialNorm L u
        ∂(sphereProbability E : Measure (UnitSphere E))) *
      intrinsicMeanWidth P L := by
  let f : L → ℝ := fun v ↦ P.directionalWidth (v : E)
  have hf (r : ℝ) (hr : 0 ≤ r) (v : L) : f (r • v) = r * f v := by
    simpa [f] using P.directionalWidth_smul_of_nonneg (v : E) hr
  have hfactor := sphereProjectionFactorization (E := E) L f hf
  have hproject (u : UnitSphere E) :
      f (L.orthogonalProjectionOnto (u : E)) =
        P.directionalWidth (u : E) := by
    change P.directionalWidth
      ((L.orthogonalProjectionOnto (u : E) : L) : E) = _
    rw [L.coe_orthogonalProjectionOnto_apply, ← hspan]
    exact P.directionalWidth_starProjection_directionSpan (u : E)
  have hnorm (u : UnitSphere E) :
      ‖L.orthogonalProjectionOnto (u : E)‖ = projectedRadialNorm L u := by
    rw [projectedRadialNorm, Submodule.coe_norm,
      L.coe_orthogonalProjectionOnto_apply]
  rw [show ambientMeanWidth P =
      ∫ u : UnitSphere E, f (L.orthogonalProjectionOnto (u : E))
        ∂(sphereProbability E : Measure (UnitSphere E)) by
      apply integral_congr_ae
      filter_upwards with u
      exact (hproject u).symm]
  rw [hfactor]
  congr 1

/-- Quantitative ambient projection bound with the exact dimension ratio. -/
theorem finrank_mul_le_ambientMeanWidth
    [Nontrivial E] (P : IntrinsicBody E) (L : Submodule ℝ E)
    [Nontrivial L] (hspan : P.directionSpan = L) {w : ℝ}
    (hw₀ : 0 ≤ w) (hw : w ≤ intrinsicMeanWidth P L) :
    (Module.finrank ℝ L : ℝ) / (Module.finrank ℝ E : ℝ) * w ≤
      ambientMeanWidth P := by
  rw [ambientMeanWidth_eq_projectedRadial_mul_intrinsicMeanWidth P L hspan]
  exact mul_le_mul
    (finrank_div_finrank_le_integral_projectedRadialNorm L) hw hw₀
    (integral_projectedRadialNorm_nonneg L)

/-- Paper-facing half-dimensional corollary: if `L` has at least half the
ambient dimension, ambient mean width is at least half the intrinsic bound. -/
theorem half_mul_le_ambientMeanWidth
    [Nontrivial E] (P : IntrinsicBody E) (L : Submodule ℝ E)
    [Nontrivial L] (hspan : P.directionSpan = L)
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ L)
    {w : ℝ} (hw₀ : 0 ≤ w) (hw : w ≤ intrinsicMeanWidth P L) :
    (1 : ℝ) / 2 * w ≤ ambientMeanWidth P := by
  rw [ambientMeanWidth_eq_projectedRadial_mul_intrinsicMeanWidth P L hspan]
  exact mul_le_mul (one_half_le_integral_projectedRadialNorm L hdim)
    hw hw₀ (integral_projectedRadialNorm_nonneg L)

theorem half_le_ambientMeanWidth_of_one_le_intrinsic
    [Nontrivial E] (P : IntrinsicBody E) (L : Submodule ℝ E)
    [Nontrivial L] (hspan : P.directionSpan = L)
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ L)
    {w : ℝ} (hw₀ : 0 ≤ w) (hw : w ≤ intrinsicMeanWidth P L) :
    w / 2 ≤ ambientMeanWidth P := by
  simpa [div_eq_mul_inv, mul_comm] using
    half_mul_le_ambientMeanWidth P L hspan hdim hw₀ hw

end ZeroOrderBounds.AccuracyImprovement
