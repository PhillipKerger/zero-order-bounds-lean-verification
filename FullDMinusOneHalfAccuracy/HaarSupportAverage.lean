import FullDMinusOneHalfAccuracy.RotationAction
import FullDMinusOneHalfAccuracy.SupportFunction
import FullDMinusOneHalfAccuracy.ConvexVolumeLimit
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Compact

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Finite approximation of Haar averages

The volumetric part of Urysohn's inequality only applies to finite Minkowski
sums.  This file supplies the functional-analytic bridge from a compact-group
average to such a finite sum.  Its first theorem is deliberately stated for
an arbitrary Bochner-integrable map: the integral belongs to the closure of
the convex hull of its range, hence can be approximated by a finite convex
combination of values of the map.

The specialization to support functions of orthogonal images is kept in this
module, while Brunn--Minkowski and volume continuity remain wholly separate.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators Matrix Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

section FiniteBochnerApproximation

variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {μ : Measure α} [IsProbabilityMeasure μ]

/-- A Bochner integral against a probability measure can be approximated in
norm by a finite convex combination of values of the integrand.  The theorem
retains the actual indices rather than only points in the range, which is the
form needed to recover finitely many rotations later. -/
theorem exists_finite_convexCombination_norm_sub_integral_lt
    (f : α → V) (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset α) (w : α → ℝ),
      (∀ i ∈ t, 0 ≤ w i) ∧
      (∑ i ∈ t, w i) = 1 ∧
      ‖(∑ i ∈ t, w i • f i) - ∫ x, f x ∂μ‖ < ε := by
  have hint : (∫ x, f x ∂μ) ∈
      closure (convexHull ℝ (Set.range f)) := by
    apply (convex_convexHull ℝ (Set.range f)).closure.integral_mem
      isClosed_closure
    · exact Filter.Eventually.of_forall fun x =>
        subset_closure (subset_convexHull ℝ (Set.range f) (mem_range_self x))
    · exact hf
  obtain ⟨g, hg, hdist⟩ := (Metric.mem_closure_iff.mp hint) ε hε
  rw [convexHull_range_eq_exists_affineCombination] at hg
  obtain ⟨t, w, hw0, hw1, hcomb⟩ := hg
  refine ⟨t, w, hw0, hw1, ?_⟩
  rw [← Finset.affineCombination_eq_linear_combination t f w hw1, hcomb]
  simpa [dist_eq_norm, norm_sub_rev] using hdist

end FiniteBochnerApproximation

/-! ## Orthogonal support profiles -/

section OrthogonalSupport

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

abbrev EuclideanCoordinateSpace := EuclideanSpace ℝ n

/-- Pull a direction back through an orthogonal matrix.  This explicit matrix
formula is convenient for joint-continuity and Haar-translation arguments. -/
def orthogonalPullback (A : Matrix.orthogonalGroup n ℝ)
    (x : EuclideanCoordinateSpace (n := n)) :
    EuclideanCoordinateSpace (n := n) :=
  WithLp.toLp 2 (star A.1 *ᵥ x.ofLp)

@[simp]
theorem orthogonalLinearIsometryEquiv_apply_eq_mulVec
    (A : Matrix.orthogonalGroup n ℝ)
    (x : EuclideanCoordinateSpace (n := n)) :
    orthogonalLinearIsometryEquiv A x =
      WithLp.toLp 2 (A.1 *ᵥ x.ofLp) :=
  rfl

@[simp]
theorem orthogonalPullback_eq_symm (A : Matrix.orthogonalGroup n ℝ)
    (x : EuclideanCoordinateSpace (n := n)) :
    orthogonalPullback A x = (orthogonalLinearIsometryEquiv A).symm x := by
  apply WithLp.ofLp_injective
  change star A.1 *ᵥ x.ofLp = Matrix.toLin' (A⁻¹).1 x.ofLp
  simp [Matrix.toLin'_apply']

/-- Pullback is jointly continuous in the orthogonal matrix and vector. -/
theorem continuous_orthogonalPullback_uncurry :
    Continuous (fun p : Matrix.orthogonalGroup n ℝ ×
        EuclideanCoordinateSpace (n := n) => orthogonalPullback p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

/-- The matrix identity used to turn left invariance of Haar measure into
rotation invariance of the averaged support profile. -/
theorem orthogonalPullback_inv_mul (A B : Matrix.orthogonalGroup n ℝ)
    (x : EuclideanCoordinateSpace (n := n)) :
    orthogonalPullback (B⁻¹ * A) x =
      orthogonalPullback A (orthogonalLinearIsometryEquiv B x) := by
  rw [orthogonalLinearIsometryEquiv_apply_eq_mulVec]
  apply WithLp.ofLp_injective
  simp only [orthogonalPullback, WithLp.ofLp_toLp]
  rw [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val, star_mul,
    star_star, Matrix.mulVec_mulVec]

/-- Upper support of an isometric image is upper support in the pulled-back
direction. -/
theorem directionalSupportSup_convexBodyLinearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) (theta : F) :
    directionalSupportSup (convexBodyLinearIsometryImage e K : Set F) theta =
      directionalSupportSup (K : Set E) (e.symm theta) := by
  obtain ⟨p, hp, hsupP, hpmax⟩ :=
    ZeroOrderBounds.IsCompact.exists_directionalSupportSup_eq
      K.isCompact K.nonempty (e.symm theta)
  have hep : e p ∈ convexBodyLinearIsometryImage e K := ⟨p, hp, rfl⟩
  rw [ZeroOrderBounds.directionalSupportSup_eq_inner_of_max
      (convexBodyLinearIsometryImage e K).isCompact
      (convexBodyLinearIsometryImage e K).nonempty theta (e p) hep,
    hsupP]
  · rw [real_inner_comm, e.inner_map_eq_flip, real_inner_comm]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    calc
      inner ℝ theta (e x) = inner ℝ (e.symm theta) x := by
        rw [real_inner_comm, e.inner_map_eq_flip, real_inner_comm]
      _ ≤ inner ℝ (e.symm theta) p := hpmax x hx
      _ = inner ℝ theta (e p) := by
        rw [real_inner_comm, ← e.inner_map_eq_flip, real_inner_comm]

/-- Matrix of a Euclidean linear isometry equivalence in the standard
orthonormal basis. -/
def orthogonalMatrixOfLinearIsometryEquiv
    (e : EuclideanCoordinateSpace (n := n) ≃ₗᵢ[ℝ]
      EuclideanCoordinateSpace (n := n)) :
    Matrix.orthogonalGroup n ℝ :=
  ⟨e.toMatrix (EuclideanSpace.basisFun n ℝ).toBasis
      (EuclideanSpace.basisFun n ℝ).toBasis,
    e.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun n ℝ)
      (EuclideanSpace.basisFun n ℝ)⟩

@[simp]
theorem orthogonalLinearIsometryEquiv_matrixOf
    (e : EuclideanCoordinateSpace (n := n) ≃ₗᵢ[ℝ]
      EuclideanCoordinateSpace (n := n)) :
    orthogonalLinearIsometryEquiv
      (orthogonalMatrixOfLinearIsometryEquiv e) = e := by
  apply LinearIsometryEquiv.ext
  intro x
  apply WithLp.ofLp_injective
  change (orthogonalMatrixOfLinearIsometryEquiv e).1 *ᵥ x.ofLp = (e x).ofLp
  exact e.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun n ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis x

/-- The matrix orthogonal group acts transitively on the unit sphere. -/
theorem exists_orthogonal_map_unitSphere
    (u v : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    ∃ A : Matrix.orthogonalGroup n ℝ,
      orthogonalLinearIsometryEquiv A
        (u : EuclideanCoordinateSpace (n := n)) = v := by
  let e : EuclideanCoordinateSpace (n := n) ≃ₗᵢ[ℝ]
      EuclideanCoordinateSpace (n := n) :=
    (ℝ ∙ ((u : EuclideanCoordinateSpace (n := n)) -
      (v : EuclideanCoordinateSpace (n := n))))ᗮ.reflection
  refine ⟨orthogonalMatrixOfLinearIsometryEquiv e, ?_⟩
  rw [orthogonalLinearIsometryEquiv_matrixOf]
  exact Submodule.reflection_sub (by simp)

/-- The support function of a rotated body, bundled as a continuous function
on the unit sphere.  It is expressed using the original body and a pulled-back
direction so that dependence on the rotation is manifestly continuous. -/
def orthogonalSupportProfile
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (A : Matrix.orthogonalGroup n ℝ) :
    C(UnitSphere (EuclideanCoordinateSpace (n := n)), ℝ) where
  toFun u := directionalSupportSup (K : Set _) (orthogonalPullback A u)
  continuous_toFun :=
    (continuous_directionalSupportSup K.isCompact).comp
      (continuous_orthogonalPullback_uncurry.comp
        (continuous_const.prodMk continuous_subtype_val))

@[simp]
theorem orthogonalSupportProfile_apply
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (A : Matrix.orthogonalGroup n ℝ)
    (u : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    orthogonalSupportProfile K A u =
      directionalSupportSup (orthogonalRotate A K : Set _)
        (u : EuclideanCoordinateSpace (n := n)) := by
  change directionalSupportSup (K : Set _)
      (orthogonalPullback A (u : EuclideanCoordinateSpace (n := n))) =
    directionalSupportSup
      (convexBodyLinearIsometryImage (orthogonalLinearIsometryEquiv A) K : Set _)
      (u : EuclideanCoordinateSpace (n := n))
  rw [directionalSupportSup_convexBodyLinearIsometryImage]
  exact congrArg (directionalSupportSup (K : Set _))
    (orthogonalPullback_eq_symm A u)

/-- The support profile varies continuously in the rotation, in uniform norm
on the sphere. -/
theorem continuous_orthogonalSupportProfile
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) :
    Continuous (orthogonalSupportProfile K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Matrix.orthogonalGroup n ℝ ×
      UnitSphere (EuclideanCoordinateSpace (n := n)) =>
    directionalSupportSup (K : Set _)
      (orthogonalPullback p.1 (p.2 : EuclideanCoordinateSpace (n := n))))
  exact (continuous_directionalSupportSup K.isCompact).comp
    (continuous_orthogonalPullback_uncurry (n := n) |>.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end OrthogonalSupport

/-! ## Support of finite Minkowski combinations -/

section FiniteMinkowskiSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem directionalSupportSup_zero_convexBody (theta : E) :
    directionalSupportSup ((0 : ConvexBody E) : Set E) theta = 0 := by
  have hmax : ∀ x ∈ (0 : ConvexBody E),
      inner ℝ theta x ≤ inner ℝ theta (0 : E) := by
    intro x hx
    change x ∈ (0 : Set E) at hx
    have hx0 : x = 0 := Set.mem_zero.mp hx
    subst x
    simp
  simpa using ZeroOrderBounds.directionalSupportSup_eq_inner_of_max
    (0 : ConvexBody E).isCompact (0 : ConvexBody E).nonempty theta 0
      (by simp) hmax

/-- Upper support commutes with a finite Minkowski sum. -/
theorem directionalSupportSup_sum_convexBody {ι : Type*} (t : Finset ι)
    (K : ι → ConvexBody E) (theta : E) :
    directionalSupportSup ((∑ i ∈ t, K i : ConvexBody E) : Set E) theta =
      ∑ i ∈ t, directionalSupportSup (K i : Set E) theta := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact directionalSupportSup_zero_convexBody theta
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ConvexBody.coe_add,
        ZeroOrderBounds.directionalSupportSup_add
          (K a).isCompact (K a).nonempty
          (∑ i ∈ t, K i).isCompact (∑ i ∈ t, K i).nonempty,
        ih]

/-- Upper support of a finite nonnegatively weighted Minkowski sum. -/
theorem directionalSupportSup_weighted_sum_convexBody {ι : Type*}
    (t : Finset ι) (w : ι → ℝ) (K : ι → ConvexBody E)
    (hw : ∀ i ∈ t, 0 ≤ w i) (theta : E) :
    directionalSupportSup
      ((∑ i ∈ t, w i • K i : ConvexBody E) : Set E) theta =
      ∑ i ∈ t, w i * directionalSupportSup (K i : Set E) theta := by
  rw [directionalSupportSup_sum_convexBody]
  apply Finset.sum_congr rfl
  intro i hi
  exact ZeroOrderBounds.directionalSupportSup_smul_set_of_nonneg
    (K i).isCompact (K i).nonempty theta (hw i hi)

end FiniteMinkowskiSupport

/-! ## Haar average of support profiles -/

section HaarSupport

universe u

variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]

local instance orthogonalMeasurableSpace :
    MeasurableSpace (Matrix.orthogonalGroup n ℝ) :=
  borel (Matrix.orthogonalGroup n ℝ)

local instance orthogonalBorelSpace :
    BorelSpace (Matrix.orthogonalGroup n ℝ) := ⟨rfl⟩

/-- Continuous support profiles are Bochner integrable against Haar
probability. -/
theorem integrable_orthogonalSupportProfile
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) :
    Integrable (orthogonalSupportProfile K)
      (orthogonalHaarProbability n :
        Measure (Matrix.orthogonalGroup n ℝ)) := by
  exact (continuous_orthogonalSupportProfile K).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The Bochner average of all rotated support profiles. -/
def haarAverageSupportProfile
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) :
    C(UnitSphere (EuclideanCoordinateSpace (n := n)), ℝ) :=
  ∫ A, orthogonalSupportProfile K A
    ∂(orthogonalHaarProbability n :
      Measure (Matrix.orthogonalGroup n ℝ))

/-- Left invariance of Haar measure makes the averaged profile invariant under
every orthogonal matrix. -/
theorem haarAverageSupportProfile_unitSphereEquiv
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (B : Matrix.orthogonalGroup n ℝ)
    (u : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    haarAverageSupportProfile K
        (unitSphereEquiv _ (orthogonalLinearIsometryEquiv B) u) =
      haarAverageSupportProfile K u := by
  have hint := integrable_orthogonalSupportProfile K
  rw [haarAverageSupportProfile, ContinuousMap.integral_apply hint,
    ContinuousMap.integral_apply hint]
  calc
    (∫ A, orthogonalSupportProfile K A
        (unitSphereEquiv _ (orthogonalLinearIsometryEquiv B) u)
        ∂(orthogonalHaarProbability n : Measure _)) =
      ∫ A, orthogonalSupportProfile K (B⁻¹ * A) u
        ∂(orthogonalHaarProbability n : Measure _) := by
          apply integral_congr_ae
          filter_upwards with A
          change directionalSupportSup (K : Set _)
              (orthogonalPullback A
                (orthogonalLinearIsometryEquiv B
                  (u : EuclideanCoordinateSpace (n := n)))) =
            directionalSupportSup (K : Set _)
              (orthogonalPullback (B⁻¹ * A)
                (u : EuclideanCoordinateSpace (n := n)))
          exact congrArg
            (fun theta : EuclideanCoordinateSpace (n := n) =>
              directionalSupportSup
                (K : Set (EuclideanCoordinateSpace (n := n))) theta)
            (orthogonalPullback_inv_mul A B u).symm
    _ = ∫ A, orthogonalSupportProfile K A u
        ∂(orthogonalHaarProbability n : Measure _) := by
      exact integral_mul_left_eq_self
        (fun A => orthogonalSupportProfile K A u) B⁻¹

/-- The Haar-averaged support profile is constant on the unit sphere. -/
theorem haarAverageSupportProfile_apply_eq
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (u v : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    haarAverageSupportProfile K u = haarAverageSupportProfile K v := by
  obtain ⟨A, hA⟩ := exists_orthogonal_map_unitSphere u v
  have huv : unitSphereEquiv _ (orthogonalLinearIsometryEquiv A) u = v := by
    apply Subtype.ext
    exact hA
  rw [← huv, haarAverageSupportProfile_unitSphereEquiv]

/-- Spherical mean of upper support.  For a difference body this is the full
spherical mean width of the original body. -/
def convexBodySphericalMeanSupport
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) : ℝ :=
  ∫ u : UnitSphere (EuclideanCoordinateSpace (n := n)),
    directionalSupportSup
      (K : Set (EuclideanCoordinateSpace (n := n)))
      (u : EuclideanCoordinateSpace (n := n))
    ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)

/-- Every rotated support profile has the same spherical integral. -/
theorem integral_orthogonalSupportProfile_sphere
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (A : Matrix.orthogonalGroup n ℝ) :
    (∫ u, orthogonalSupportProfile K A u
      ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)) =
      convexBodySphericalMeanSupport K := by
  let e := orthogonalLinearIsometryEquiv A
  have hpres : MeasurePreserving
      (unitSphereEquiv (EuclideanCoordinateSpace (n := n)) e.symm)
      (sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)
      (sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) :=
    ⟨(unitSphereEquiv _ e.symm).measurable,
      map_sphereProbability_unitSphereEquiv _ e.symm⟩
  calc
    (∫ u, orthogonalSupportProfile K A u
      ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)) =
      ∫ u, directionalSupportSup
        (K : Set (EuclideanCoordinateSpace (n := n)))
        ((unitSphereEquiv _ e.symm u :
          UnitSphere (EuclideanCoordinateSpace (n := n))) :
          EuclideanCoordinateSpace (n := n))
        ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) := by
          apply integral_congr_ae
          filter_upwards with u
          change directionalSupportSup
              (K : Set (EuclideanCoordinateSpace (n := n)))
              (orthogonalPullback A
                (u : EuclideanCoordinateSpace (n := n))) =
            directionalSupportSup
              (K : Set (EuclideanCoordinateSpace (n := n)))
              ((orthogonalLinearIsometryEquiv A).symm
                (u : EuclideanCoordinateSpace (n := n)))
          exact congrArg
            (fun theta : EuclideanCoordinateSpace (n := n) =>
              directionalSupportSup
                (K : Set (EuclideanCoordinateSpace (n := n))) theta)
            (orthogonalPullback_eq_symm A u)
    _ = convexBodySphericalMeanSupport K := by
      rw [convexBodySphericalMeanSupport]
      exact hpres.integral_comp
        (unitSphereEquiv _ e.symm).measurableEmbedding
        (fun u : UnitSphere (EuclideanCoordinateSpace (n := n)) =>
          directionalSupportSup
            (K : Set (EuclideanCoordinateSpace (n := n)))
            (u : EuclideanCoordinateSpace (n := n)))

/-- Joint integrability needed for the Fubini step identifying the constant
Haar average. -/
theorem integrable_orthogonalSupportProfile_uncurry
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) :
    Integrable (Function.uncurry fun A u => orthogonalSupportProfile K A u)
      ((orthogonalHaarProbability n :
          Measure (Matrix.orthogonalGroup n ℝ)).prod
        (sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_eval.comp
      ((continuous_orthogonalSupportProfile K).comp continuous_fst |>.prodMk
        continuous_snd)
  · exact HasCompactSupport.of_compactSpace _

/-- The exact value of the constant Haar average is spherical mean support. -/
theorem haarAverageSupportProfile_apply_eq_meanSupport
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (u : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    haarAverageSupportProfile K u = convexBodySphericalMeanSupport K := by
  have hJoint := integrable_orthogonalSupportProfile_uncurry K
  calc
    haarAverageSupportProfile K u =
        ∫ v : UnitSphere (EuclideanCoordinateSpace (n := n)),
          haarAverageSupportProfile K v
          ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) := by
      calc
        haarAverageSupportProfile K u =
            ∫ _v : UnitSphere (EuclideanCoordinateSpace (n := n)),
              haarAverageSupportProfile K u
              ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) := by
          simp
        _ = ∫ v, haarAverageSupportProfile K v
              ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) := by
          apply integral_congr_ae
          filter_upwards with v
          exact haarAverageSupportProfile_apply_eq K u v
    _ = ∫ v, ∫ A, orthogonalSupportProfile K A v
          ∂(orthogonalHaarProbability n : Measure _)
          ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _) := by
      apply integral_congr_ae
      filter_upwards with v
      exact ContinuousMap.integral_apply
        (integrable_orthogonalSupportProfile K) v
    _ = ∫ A, ∫ v, orthogonalSupportProfile K A v
          ∂(sphereProbability (EuclideanCoordinateSpace (n := n)) : Measure _)
          ∂(orthogonalHaarProbability n : Measure _) :=
      (integral_integral_swap hJoint).symm
    _ = convexBodySphericalMeanSupport K := by
      simp_rw [integral_orthogonalSupportProfile_sphere K]
      simp

/-- Mean support of the difference body is full mean width. -/
theorem convexBodySphericalMeanSupport_difference
    (K : ConvexBody (EuclideanCoordinateSpace (n := n))) :
    convexBodySphericalMeanSupport (convexBodyDifference K) =
      convexBodySphericalMeanWidth K := by
  rw [convexBodySphericalMeanSupport, convexBodySphericalMeanWidth]
  apply integral_congr_ae
  filter_upwards with u
  exact directionalSupportSup_convexBodyDifference K u

/-- In the difference-body form used for Urysohn, the exact Haar average is
the full spherical mean width. -/
theorem haarAverageDifferenceSupportProfile_apply
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (u : UnitSphere (EuclideanCoordinateSpace (n := n))) :
    haarAverageSupportProfile (convexBodyDifference K) u =
      convexBodySphericalMeanWidth K := by
  rw [haarAverageSupportProfile_apply_eq_meanSupport,
    convexBodySphericalMeanSupport_difference]

/-- A finite convex combination of rotated support profiles uniformly
approximates the exact Haar average. -/
theorem exists_finite_orthogonal_supportProfiles_close_meanSupport
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset (Matrix.orthogonalGroup n ℝ))
        (w : Matrix.orthogonalGroup n ℝ → ℝ),
      (∀ A ∈ t, 0 ≤ w A) ∧
      (∑ A ∈ t, w A) = 1 ∧
      ∀ u : UnitSphere (EuclideanCoordinateSpace (n := n)),
        |(∑ A ∈ t, w A *
            directionalSupportSup (orthogonalRotate A K : Set _)
              (u : EuclideanCoordinateSpace (n := n))) -
          convexBodySphericalMeanSupport K| < ε := by
  obtain ⟨t, w, hw0, hw1, hclose⟩ :=
    exists_finite_convexCombination_norm_sub_integral_lt
      (orthogonalSupportProfile K) (integrable_orthogonalSupportProfile K) hε
  refine ⟨t, w, hw0, hw1, fun u => ?_⟩
  have hpoint := ContinuousMap.norm_coe_le_norm
    ((∑ A ∈ t, w A • orthogonalSupportProfile K A) -
      haarAverageSupportProfile K) u
  have hlt := lt_of_le_of_lt hpoint hclose
  rw [Real.norm_eq_abs] at hlt
  simpa only [ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, orthogonalSupportProfile_apply,
    haarAverageSupportProfile_apply_eq_meanSupport] using hlt

/-- Difference-body specialization: the limiting constant is the full mean
width of the original body. -/
theorem exists_finite_rotated_difference_support_close_meanWidth
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset (Matrix.orthogonalGroup n ℝ))
        (w : Matrix.orthogonalGroup n ℝ → ℝ),
      (∀ A ∈ t, 0 ≤ w A) ∧
      (∑ A ∈ t, w A) = 1 ∧
      ∀ u : UnitSphere (EuclideanCoordinateSpace (n := n)),
        |(∑ A ∈ t, w A *
            directionalSupportSup
              (orthogonalRotate A (convexBodyDifference K) : Set _)
              (u : EuclideanCoordinateSpace (n := n))) -
          convexBodySphericalMeanWidth K| < ε := by
  simpa only [convexBodySphericalMeanSupport_difference] using
    exists_finite_orthogonal_supportProfiles_close_meanSupport
      (convexBodyDifference K) hε

/-- The actual finite weighted Minkowski body corresponding to the support
profile combination. -/
def finiteRotatedMinkowskiCombination
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (t : Finset (Matrix.orthogonalGroup n ℝ))
    (w : Matrix.orthogonalGroup n ℝ → ℝ) :
    ConvexBody (EuclideanCoordinateSpace (n := n)) :=
  ∑ A ∈ t, w A • orthogonalRotate A K

/-- Exact support formula for the finite weighted rotated body. -/
theorem directionalSupportSup_finiteRotatedMinkowskiCombination
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    (t : Finset (Matrix.orthogonalGroup n ℝ))
    (w : Matrix.orthogonalGroup n ℝ → ℝ)
    (hw : ∀ A ∈ t, 0 ≤ w A)
    (theta : EuclideanCoordinateSpace (n := n)) :
    directionalSupportSup
      (finiteRotatedMinkowskiCombination K t w : Set _) theta =
      ∑ A ∈ t, w A *
        directionalSupportSup (orthogonalRotate A K : Set _) theta := by
  exact directionalSupportSup_weighted_sum_convexBody t w
    (fun A => orthogonalRotate A K) hw theta

/-- Audit-facing finite approximation theorem: for every positive tolerance,
one concrete convex combination of rotated difference bodies lies in the ball
whose radius is full mean width plus that tolerance.  No Brunn--Minkowski
inequality is used here. -/
theorem exists_finite_rotated_difference_minkowskiCombination_subset_closedBall
    (K : ConvexBody (EuclideanCoordinateSpace (n := n)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset (Matrix.orthogonalGroup n ℝ))
        (w : Matrix.orthogonalGroup n ℝ → ℝ),
      (∀ A ∈ t, 0 ≤ w A) ∧
      (∑ A ∈ t, w A) = 1 ∧
      (finiteRotatedMinkowskiCombination (convexBodyDifference K) t w : Set _)
        ⊆ closedBall (0 : EuclideanCoordinateSpace (n := n))
          (convexBodySphericalMeanWidth K + ε) ∧
      ∀ u : UnitSphere (EuclideanCoordinateSpace (n := n)),
        |directionalSupportSup
            (finiteRotatedMinkowskiCombination
              (convexBodyDifference K) t w : Set _)
            (u : EuclideanCoordinateSpace (n := n)) -
          convexBodySphericalMeanWidth K| < ε := by
  obtain ⟨t, w, hw, hwsum, hclose⟩ :=
    exists_finite_rotated_difference_support_close_meanWidth K hε
  refine ⟨t, w, hw, hwsum, ?_, ?_⟩
  · apply subset_closedBall_of_directionalSupportSup_le
      (finiteRotatedMinkowskiCombination
        (convexBodyDifference K) t w).isCompact
      (finiteRotatedMinkowskiCombination
        (convexBodyDifference K) t w).nonempty
    intro theta htheta
    let u : UnitSphere (EuclideanCoordinateSpace (n := n)) :=
      ⟨theta, by simpa [mem_sphere_zero_iff_norm] using htheta⟩
    have habs := hclose u
    rw [directionalSupportSup_finiteRotatedMinkowskiCombination
      (convexBodyDifference K) t w hw theta]
    have hdiff :
        (∑ A ∈ t, w A *
            directionalSupportSup
              (orthogonalRotate A (convexBodyDifference K) : Set _)
              theta) - convexBodySphericalMeanWidth K < ε := by
      exact (le_abs_self _).trans_lt (by simpa [u] using habs)
    linarith
  · intro u
    rw [directionalSupportSup_finiteRotatedMinkowskiCombination
      (convexBodyDifference K) t w hw]
    exact hclose u

end HaarSupport

end ZeroOrderBounds.AccuracyImprovement
