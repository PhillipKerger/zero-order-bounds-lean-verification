import FullDMinusOneHalfAccuracy.SphereMeasure
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Polar factorization through an orthogonal subspace

This module proves the spherical disintegration identity needed by the
improved-accuracy argument.  The proof avoids beta-distribution formulas.
It inserts the radial Gaussian weight `exp (-‖x‖²)`, uses Mathlib's polar
decomposition and the volume-preserving orthogonal decomposition
`E ≃ L ×₂ Lᵮ`, and finally cancels two strictly positive radial constants.
-/

noncomputable section

open scoped ENNReal NNReal Pointwise RealInnerProductSpace
open MeasureTheory Metric Set

namespace ZeroOrderBounds.AccuracyImprovement

/-- The radial first-moment factor occurring in the polar integral of a
degree-one homogeneous function. -/
def radialGaussianFirst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : ℝ :=
  ∫ r : Ioi (0 : ℝ), Real.exp (-r.1 ^ 2) * r.1
    ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)

/-- Polar integration of a degree-one homogeneous function against a radial
Gaussian.  No integrability hypothesis is needed for the equality, because
the Bochner integral and product-integral identities use the same
nonintegrable convention on both sides. -/
theorem integral_gaussian_mul_oneHomogeneous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (f : E → ℝ)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ x, f (r • x) = r * f x) :
    (∫ x : E, Real.exp (-‖x‖ ^ 2) * f x) =
      (∫ u : UnitSphere E, f (u : E) ∂(volume : Measure E).toSphere) *
        radialGaussianFirst E := by
  calc
    (∫ x : E, Real.exp (-‖x‖ ^ 2) * f x) =
        ∫ x : ({0}ᶜ : Set E), Real.exp (-‖(x : E)‖ ^ 2) * f (x : E)
          ∂((volume : Measure E).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x : E ↦ Real.exp (-‖x‖ ^ 2) * f x), restrict_compl_singleton]
    _ = ∫ ur : UnitSphere E × Ioi (0 : ℝ),
          Real.exp (-ur.2.1 ^ 2) * f (ur.2.1 • (ur.1 : E))
          ∂((volume : Measure E).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      let g : UnitSphere E × Ioi (0 : ℝ) → ℝ := fun ur ↦
        Real.exp (-ur.2.1 ^ 2) * f (ur.2.1 • (ur.1 : E))
      rw [← (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (homeomorphUnitSphereProd E).measurableEmbedding g]
      apply integral_congr_ae
      filter_upwards with x
      simp only [g, homeomorphUnitSphereProd_apply_snd_coe,
        homeomorphUnitSphereProd_apply_fst_coe]
      have hx : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
      rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
    _ = ∫ ur : UnitSphere E × Ioi (0 : ℝ),
          f (ur.1 : E) * (Real.exp (-ur.2.1 ^ 2) * ur.2.1)
          ∂((volume : Measure E).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      apply integral_congr_ae
      filter_upwards with ur
      rw [hsmul ur.2.1 ur.2.2.le]
      ring
    _ = _ := by
      simpa [radialGaussianFirst] using
        (integral_prod_mul (μ := (volume : Measure E).toSphere)
          (ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          (fun u : UnitSphere E ↦ f (u : E))
          (fun r : Ioi (0 : ℝ) ↦ Real.exp (-r.1 ^ 2) * r.1))

/-- Orthogonal Gaussian integration factors into the target subspace and its
orthogonal complement. -/
theorem integral_gaussian_projection_factor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E) (f : L → ℝ) :
    (∫ x : E, Real.exp (-‖x‖ ^ 2) * f (L.orthogonalProjectionOnto x)) =
      (∫ y : L, Real.exp (-‖y‖ ^ 2) * f y) *
        ∫ z : Lᗮ, Real.exp (-‖z‖ ^ 2) := by
  let e : E ≃ᵐ (L × Lᗮ) :=
    L.orthogonalDecomposition.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (L × Lᗮ)).symm
  have hp : MeasurePreserving e :=
    (LinearIsometryEquiv.measurePreserving L.orthogonalDecomposition).trans
      (WithLp.volume_preserving_ofLp L Lᗮ)
  calc
    (∫ x : E, Real.exp (-‖x‖ ^ 2) * f (L.orthogonalProjectionOnto x)) =
        ∫ yz : L × Lᗮ,
          (Real.exp (-‖yz.1‖ ^ 2) * f yz.1) * Real.exp (-‖yz.2‖ ^ 2) := by
      rw [← hp.integral_comp e.measurableEmbedding]
      apply integral_congr_ae
      filter_upwards with x
      simp only [e, MeasurableEquiv.trans_apply,
        LinearIsometryEquiv.coe_toMeasurableEquiv,
        Submodule.orthogonalDecomposition_apply,
        MeasurableEquiv.toLp_symm_apply]
      rw [show ‖x‖ ^ 2 = ‖L.orthogonalProjectionOnto x‖ ^ 2 +
          ‖Lᗮ.orthogonalProjectionOnto x‖ ^ 2 by
        simpa only [← Submodule.coe_norm] using L.norm_sq_eq_add_norm_sq_projection x]
      rw [neg_add, Real.exp_add]
      ring
    _ = _ := by
      simpa only [Measure.volume_eq_prod] using
        (integral_prod_mul (μ := (volume : Measure L)) (ν := (volume : Measure Lᗮ))
          (fun y : L ↦ Real.exp (-‖y‖ ^ 2) * f y)
          (fun z : Lᗮ ↦ Real.exp (-‖z‖ ^ 2)))

/-- Integrability of the radial constant. -/
theorem integrable_radialGaussianFirst (n : ℕ) (hn : 0 < n) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ Real.exp (-r.1 ^ 2) * r.1)
      (Measure.volumeIoiPow (n - 1)) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul']
  · have hbase := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 : ℝ)) (by norm_num) (s := (n : ℝ)) (by
        have hn₀ : 0 ≤ (n : ℝ) := by positivity
        linarith)
    have hsub := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hbase
    apply hsub.congr
    filter_upwards with r
    simp only [Function.comp_apply,
      ENNReal.toReal_ofReal (pow_nonneg r.2.le _)]
    rw [Real.rpow_natCast]
    simp only [one_mul, smul_eq_mul]
    have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    conv_lhs => rw [hn_eq, pow_succ]
    ring
  · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
  · exact ae_of_all _ fun _ ↦ by simp

/-- Strict positivity of the radial factor is what licenses cancellation in
the spherical factorization proof. -/
theorem radialGaussianFirst_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] : 0 < radialGaussianFirst E := by
  let n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  rw [radialGaussianFirst, integral_pos_iff_support_of_nonneg
    (fun r ↦ mul_nonneg (Real.exp_pos _).le r.2.le)
    (integrable_radialGaussianFirst n hn)]
  have hsupport : Function.support (fun r : Ioi (0 : ℝ) ↦
      Real.exp (-r.1 ^ 2) * r.1) = Set.univ := by
    ext r
    have hr : (r : ℝ) ≠ 0 := ne_of_gt r.2
    simp [Function.mem_support, hr]
  rw [hsupport]
  apply Measure.measure_univ_pos.mpr
  intro hzero
  have hI := congrArg
    (fun μ : Measure (Ioi (0 : ℝ)) ↦
      μ (Iio (⟨1, by norm_num⟩ : Ioi (0 : ℝ)))) hzero
  rw [Measure.volumeIoiPow_apply_Iio] at hI
  simp at hI
  have hpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) + 1 := by positivity
  exact (not_lt_of_ge hI) hpos

/-- Cross-multiplied spherical factorization for unnormalized surface
measures. -/
theorem rawSphereProjectionFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (L : Submodule ℝ E) [Nontrivial L] (f : L → ℝ)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ x, f (r • x) = r * f x) :
    (∫ u : UnitSphere E, f (L.orthogonalProjectionOnto (u : E))
        ∂(volume : Measure E).toSphere) *
      (∫ v : UnitSphere L, ‖(v : L)‖ ∂(volume : Measure L).toSphere) =
    (∫ u : UnitSphere E, ‖L.orthogonalProjectionOnto (u : E)‖
        ∂(volume : Measure E).toSphere) *
      (∫ v : UnitSphere L, f (v : L) ∂(volume : Measure L).toSphere) := by
  let fA : E → ℝ := fun x ↦ f (L.orthogonalProjectionOnto x)
  let nA : E → ℝ := fun x ↦ ‖L.orthogonalProjectionOnto x‖
  let nL : L → ℝ := fun x ↦ ‖x‖
  have hfA (r : ℝ) (hr : 0 ≤ r) (x : E) : fA (r • x) = r * fA x := by
    simp only [fA, map_smul]
    exact hsmul r hr _
  have hnA (r : ℝ) (hr : 0 ≤ r) (x : E) : nA (r • x) = r * nA x := by
    simp [nA, norm_smul, abs_of_nonneg hr]
  have hnL (r : ℝ) (hr : 0 ≤ r) (x : L) : nL (r • x) = r * nL x := by
    simp [nL, norm_smul, abs_of_nonneg hr]
  have hpAf := integral_gaussian_mul_oneHomogeneous (E := E) fA hfA
  have hpAn := integral_gaussian_mul_oneHomogeneous (E := E) nA hnA
  have hpLf := integral_gaussian_mul_oneHomogeneous (E := L) f hsmul
  have hpLn := integral_gaussian_mul_oneHomogeneous (E := L) nL hnL
  have hgAf := integral_gaussian_projection_factor (E := E) L f
  have hgAn := integral_gaussian_projection_factor (E := E) L nL
  have hcross :
      (∫ x : E, Real.exp (-‖x‖ ^ 2) * fA x) *
          (∫ y : L, Real.exp (-‖y‖ ^ 2) * nL y) =
        (∫ x : E, Real.exp (-‖x‖ ^ 2) * nA x) *
          (∫ y : L, Real.exp (-‖y‖ ^ 2) * f y) := by
    rw [show (∫ x : E, Real.exp (-‖x‖ ^ 2) * fA x) =
        (∫ x : E, Real.exp (-‖x‖ ^ 2) *
          f (L.orthogonalProjectionOnto x)) by rfl, hgAf]
    rw [show (∫ x : E, Real.exp (-‖x‖ ^ 2) * nA x) =
        (∫ x : E, Real.exp (-‖x‖ ^ 2) *
          nL (L.orthogonalProjectionOnto x)) by rfl, hgAn]
    ring
  rw [hpAf, hpAn, hpLf, hpLn] at hcross
  apply mul_left_cancel₀
    (mul_ne_zero (radialGaussianFirst_pos (E := E)).ne'
      (radialGaussianFirst_pos (E := L)).ne')
  convert hcross using 1 <;> ring

/-- Real total mass of unnormalized Euclidean surface measure. -/
def surfaceMassReal (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : ℝ :=
  ((sphereFiniteMeasure E).mass : ℝ)

/-- Converting an unnormalized spherical integral to normalized probability
multiplies it by the real surface mass. -/
theorem rawSphereIntegral_eq_mass_mul_probability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (f : UnitSphere E → ℝ) :
    (∫ u, f u ∂(volume : Measure E).toSphere) =
      surfaceMassReal E *
        ∫ u, f u ∂(sphereProbability E : Measure (UnitSphere E)) := by
  letI : Nonempty (UnitSphere E) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort
  let μ : FiniteMeasure (UnitSphere E) := sphereFiniteMeasure E
  have hμ : μ ≠ 0 := by simpa [μ] using sphereFiniteMeasure_ne_zero E
  have hμmeasure : (μ : Measure (UnitSphere E)) ≠ 0 := by
    intro h
    apply hμ
    apply FiniteMeasure.toMeasure_injective
    simpa using h
  have hmassENN : 0 < (↑μ.mass : ℝ≥0∞) := by
    rw [FiniteMeasure.ennreal_mass]
    exact Measure.measure_univ_pos.mpr hμmeasure
  have hmassNN : μ.mass ≠ 0 := by exact_mod_cast hmassENN.ne'
  have hnorm : (sphereProbability E : Measure (UnitSphere E)) =
      μ.mass⁻¹ • (μ : Measure (UnitSphere E)) := by
    change ((μ.normalize : ProbabilityMeasure (UnitSphere E)) :
      Measure (UnitSphere E)) = _
    exact μ.toMeasure_normalize_eq_of_nonzero hμ
  rw [hnorm, integral_smul_nnreal_measure]
  change (∫ u, f u ∂(μ : Measure (UnitSphere E))) =
    (μ.mass : ℝ) * ((μ.mass⁻¹ : NNReal) •
      ∫ u, f u ∂(μ : Measure (UnitSphere E)))
  simp [NNReal.smul_def, hmassNN]

theorem surfaceMassReal_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] : 0 < surfaceMassReal E := by
  let μ : FiniteMeasure (UnitSphere E) := sphereFiniteMeasure E
  have hμ : μ ≠ 0 := by simpa [μ] using sphereFiniteMeasure_ne_zero E
  have hμmeasure : (μ : Measure (UnitSphere E)) ≠ 0 := by
    intro h
    apply hμ
    apply FiniteMeasure.toMeasure_injective
    simpa using h
  change 0 < (μ.mass : ℝ)
  exact_mod_cast (show 0 < (↑μ.mass : ℝ≥0∞) by
    rw [FiniteMeasure.ennreal_mass]
    exact Measure.measure_univ_pos.mpr hμmeasure)

/-- Normalized spherical projection factorization.  This is the formal
subspace-disintegration theorem used by the optimization argument. -/
theorem sphereProjectionFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (L : Submodule ℝ E) [Nontrivial L] (f : L → ℝ)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ x, f (r • x) = r * f x) :
    (∫ u : UnitSphere E, f (L.orthogonalProjectionOnto (u : E))
        ∂(sphereProbability E : Measure (UnitSphere E))) =
      (∫ u : UnitSphere E, ‖L.orthogonalProjectionOnto (u : E)‖
          ∂(sphereProbability E : Measure (UnitSphere E))) *
        ∫ v : UnitSphere L, f (v : L)
          ∂(sphereProbability L : Measure (UnitSphere L)) := by
  have hraw := rawSphereProjectionFactorization (E := E) L f hsmul
  rw [rawSphereIntegral_eq_mass_mul_probability (E := E)
      (fun u : UnitSphere E ↦ f (L.orthogonalProjectionOnto (u : E))),
    rawSphereIntegral_eq_mass_mul_probability (E := L)
      (fun v : UnitSphere L ↦ ‖(v : L)‖),
    rawSphereIntegral_eq_mass_mul_probability (E := E)
      (fun u : UnitSphere E ↦ ‖L.orthogonalProjectionOnto (u : E)‖),
    rawSphereIntegral_eq_mass_mul_probability (E := L)
      (fun v : UnitSphere L ↦ f (v : L))] at hraw
  have hnorm : (∫ v : UnitSphere L, ‖(v : L)‖
      ∂(sphereProbability L : Measure (UnitSphere L))) = 1 := by simp
  rw [hnorm] at hraw
  apply mul_left_cancel₀
    (mul_ne_zero (surfaceMassReal_pos (E := E)).ne'
      (surfaceMassReal_pos (E := L)).ne')
  convert hraw using 1 <;> ring

end ZeroOrderBounds.AccuracyImprovement
