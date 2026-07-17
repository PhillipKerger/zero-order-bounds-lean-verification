import FullDMinusOneHalfAccuracy.HaarSupportAverage
import FullDMinusOneHalfAccuracy.FiniteBrunnMinkowski
import FullDMinusOneHalfAccuracy.IntrinsicCoordinates
import ZeroOrderBounds.BallVolumeRatio

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Assembly of Urysohn's inequality

This file contains the rotation-averaging and limiting part of Urysohn's
inequality.  The general midpoint Brunn--Minkowski theorem is an ordinary
premise: once that theorem is supplied, every remaining step below is
verified without additional assumptions.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

universe u

/-- Radius of the Euclidean ball having the same volume as `K`. -/
def convexBodyNormalizedVolumeRadius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) : ℝ :=
  (convexBodyVolumeReal K / kappaReal (Module.finrank ℝ E)) ^
    ((Module.finrank ℝ E : ℝ)⁻¹)

section EuclideanCoordinates

variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]

abbrev CoordinateSpace := EuclideanSpace ℝ n

/-- Linear isometries preserve the real volume used in the homogeneous
volume root. -/
theorem convexBodyVolumeReal_linearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    convexBodyVolumeReal (convexBodyLinearIsometryImage e K) =
      convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal,
    volume_convexBodyLinearIsometryImage]

/-- Linear isometries between equal-dimensional Euclidean spaces preserve
the homogeneous volume root. -/
theorem convexBodyVolumeRoot_linearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    convexBodyVolumeRoot (convexBodyLinearIsometryImage e K) =
      convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_linearIsometryImage, e.finrank_eq]

/-- The equal-volume radius is invariant under a Euclidean linear isometry. -/
theorem convexBodyNormalizedVolumeRadius_linearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    convexBodyNormalizedVolumeRadius
        (convexBodyLinearIsometryImage e K) =
      convexBodyNormalizedVolumeRadius K := by
  rw [convexBodyNormalizedVolumeRadius, convexBodyNormalizedVolumeRadius,
    convexBodyVolumeReal_linearIsometryImage, e.finrank_eq]

/-- Spherical mean width is invariant under a Euclidean linear isometry. -/
theorem convexBodySphericalMeanWidth_linearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [Nontrivial E] [Nontrivial F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    convexBodySphericalMeanWidth (convexBodyLinearIsometryImage e K) =
      convexBodySphericalMeanWidth K := by
  have hpres : MeasurePreserving (unitSphereEquiv F e.symm)
      (sphereProbability F : Measure (UnitSphere F))
      (sphereProbability E : Measure (UnitSphere E)) :=
    ⟨(unitSphereEquiv F e.symm).measurable,
      map_sphereProbability_unitSphereEquiv F e.symm⟩
  rw [convexBodySphericalMeanWidth, convexBodySphericalMeanWidth]
  calc
    (∫ u : UnitSphere F,
        directionalWidth
          (convexBodyLinearIsometryImage e K : Set F) (u : F)
        ∂(sphereProbability F : Measure (UnitSphere F))) =
      ∫ u : UnitSphere F,
        directionalWidth (K : Set E)
          ((unitSphereEquiv F e.symm u : UnitSphere E) : E)
        ∂(sphereProbability F : Measure (UnitSphere F)) := by
          apply integral_congr_ae
          filter_upwards with u
          exact directionalWidth_convexBodyLinearIsometryImage e K u
    _ = ∫ v : UnitSphere E, directionalWidth (K : Set E) (v : E)
          ∂(sphereProbability E : Measure (UnitSphere E)) := by
      exact hpres.integral_comp
        (unitSphereEquiv F e.symm).measurableEmbedding
        (fun v : UnitSphere E => directionalWidth (K : Set E) (v : E))

/-- The finite rotation averages produced by Haar approximation all have at
least the volume of the doubled original body. -/
theorem volume_two_smul_le_finiteRotatedDifferenceCombination
    (hBM : ∀ K L : ConvexBody (CoordinateSpace (n := n)),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K : ConvexBody (CoordinateSpace (n := n)))
    (t : Finset (Matrix.orthogonalGroup n ℝ))
    (w : Matrix.orthogonalGroup n ℝ → ℝ)
    (hw : ∀ A ∈ t, 0 ≤ w A) (hwsum : (∑ A ∈ t, w A) = 1) :
    volume ((2 : ℝ) • K : Set (CoordinateSpace (n := n))) ≤
      volume (finiteRotatedMinkowskiCombination
        (convexBodyDifference K) t w : Set (CoordinateSpace (n := n))) := by
  have hdim : Module.finrank ℝ (CoordinateSpace (n := n)) ≠ 0 := by
    rw [finrank_euclideanSpace]
    exact Fintype.card_ne_zero
  have hfinite := sum_weighted_convexBodyVolumeRoot_le hdim hBM t w
    (fun A => orthogonalRotate A (convexBodyDifference K)) hw
  have hrootDifference :
      convexBodyVolumeRoot (convexBodyDifference K) ≤
        convexBodyVolumeRoot
          (finiteRotatedMinkowskiCombination (convexBodyDifference K) t w) := by
    calc
      convexBodyVolumeRoot (convexBodyDifference K) =
          (∑ A ∈ t, w A) * convexBodyVolumeRoot (convexBodyDifference K) := by
            rw [hwsum, one_mul]
      _ = ∑ A ∈ t,
          w A * convexBodyVolumeRoot
            (orthogonalRotate A (convexBodyDifference K)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro A hA
            rw [convexBodyVolumeRoot_orthogonalRotate]
      _ ≤ convexBodyVolumeRoot
          (finiteRotatedMinkowskiCombination (convexBodyDifference K) t w) :=
            hfinite
  have hroot : convexBodyVolumeRoot ((2 : ℝ) • K) ≤
      convexBodyVolumeRoot
        (finiteRotatedMinkowskiCombination (convexBodyDifference K) t w) := by
    rw [convexBodyVolumeRoot_smul_of_nonneg K hdim (by norm_num)]
    exact (two_mul_convexBodyVolumeRoot_le_difference hdim hBM K).trans
      hrootDifference
  exact volume_le_volume_of_convexBodyVolumeRoot_le hdim hroot

/-- Rotation averaging, finite Brunn--Minkowski, and continuity from above
give the core volumetric form of Urysohn: the doubled body has no more volume
than the ball whose radius is its full spherical mean width. -/
theorem volume_two_smul_le_closedBall_sphericalMeanWidth
    (hBM : ∀ K L : ConvexBody (CoordinateSpace (n := n)),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K : ConvexBody (CoordinateSpace (n := n))) :
    volume ((2 : ℝ) • K : Set (CoordinateSpace (n := n))) ≤
      volume (closedBall (0 : CoordinateSpace (n := n))
        (convexBodySphericalMeanWidth K)) := by
  apply volume_le_closedBall_of_forall_pos
  intro ε hε
  obtain ⟨t, w, hw, hwsum, hsubset, _hclose⟩ :=
    exists_finite_rotated_difference_minkowskiCombination_subset_closedBall
      K hε
  exact (volume_two_smul_le_finiteRotatedDifferenceCombination
    hBM K t w hw hwsum).trans (measure_mono hsubset)

/-- Full-dimensional Urysohn inequality in Euclidean coordinates.  Our mean
width is the integral of the full width, so the conventional volume radius
appears with the sharp factor `2`. -/
theorem two_mul_convexBodyNormalizedVolumeRadius_le_sphericalMeanWidth
    (hBM : ∀ K L : ConvexBody (CoordinateSpace (n := n)),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K : ConvexBody (CoordinateSpace (n := n))) :
    2 * convexBodyNormalizedVolumeRadius K ≤
      convexBodySphericalMeanWidth K := by
  let d := Fintype.card n
  have hd : d ≠ 0 := Fintype.card_ne_zero
  have hfinrank : Module.finrank ℝ (CoordinateSpace (n := n)) = d :=
    finrank_euclideanSpace
  have hwidth : 0 ≤ convexBodySphericalMeanWidth K :=
    ConvexBody.sphericalMeanWidth_nonneg K
  have hvol := volume_two_smul_le_closedBall_sphericalMeanWidth hBM K
  have hreal := ENNReal.toReal_mono measure_closedBall_lt_top.ne hvol
  change convexBodyVolumeReal ((2 : ℝ) • K) ≤
    (volume (closedBall (0 : CoordinateSpace (n := n))
      (convexBodySphericalMeanWidth K))).toReal at hreal
  rw [convexBodyVolumeReal_smul_of_nonneg K (by norm_num), hfinrank,
    volume_closedBall_eq_rpow_mul_kappa hfinrank hd,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hwidth] at hreal
  change 2 ^ d * convexBodyVolumeReal K ≤
    convexBodySphericalMeanWidth K ^ d * kappaReal d at hreal
  have hkappa : 0 < kappaReal d := kappaReal_pos d
  have hratio : 0 ≤ convexBodyVolumeReal K / kappaReal d :=
    div_nonneg (convexBodyVolumeReal_nonneg K) hkappa.le
  have hdiv :
      2 ^ d * (convexBodyVolumeReal K / kappaReal d) ≤
        convexBodySphericalMeanWidth K ^ d := by
    have := (div_le_iff₀ hkappa).2 hreal
    simpa [mul_div_assoc] using this
  have hroot := Real.rpow_le_rpow
    (mul_nonneg (pow_nonneg (by norm_num) d) hratio) hdiv
    (inv_nonneg.mpr (Nat.cast_nonneg d))
  rw [Real.mul_rpow (pow_nonneg (by norm_num) d) hratio,
    Real.pow_rpow_inv_natCast (by norm_num) hd,
    Real.pow_rpow_inv_natCast hwidth hd] at hroot
  simpa [convexBodyNormalizedVolumeRadius, hfinrank, d] using hroot

/-- Equivalent half-mean-width presentation of full-dimensional Urysohn. -/
theorem convexBodyNormalizedVolumeRadius_le_half_sphericalMeanWidth
    (hBM : ∀ K L : ConvexBody (CoordinateSpace (n := n)),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K : ConvexBody (CoordinateSpace (n := n))) :
    convexBodyNormalizedVolumeRadius K ≤
      convexBodySphericalMeanWidth K / 2 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using
    two_mul_convexBodyNormalizedVolumeRadius_le_sphericalMeanWidth hBM K

end EuclideanCoordinates

section IntrinsicBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Intrinsic Urysohn inequality.  The premise is midpoint
Brunn--Minkowski in the standard Euclidean coordinate space of the affine
hull.  This is the exact form needed for lower-dimensional row bodies. -/
theorem two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth
    (P : IntrinsicBody E) [Nontrivial P.directionSpan] (hdim : P.dim ≠ 0)
    (hBM : ∀ K L : ConvexBody
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ P.directionSpan))),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L) :
    2 * (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) ≤
      intrinsicMeanWidth P P.directionSpan := by
  have hdir : Module.finrank ℝ P.directionSpan ≠ 0 := by
    simpa only [finrank_directionSpan_eq_dim] using hdim
  letI : Nonempty (Fin (Module.finrank ℝ P.directionSpan)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hdir)
  let e : P.directionSpan ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ P.directionSpan)) :=
    (stdOrthonormalBasis ℝ P.directionSpan).repr
  let K := convexBodyLinearIsometryImage e
    (IntrinsicCoordinates.coordinateBody P)
  have hU :=
    two_mul_convexBodyNormalizedVolumeRadius_le_sphericalMeanWidth hBM K
  rw [convexBodyNormalizedVolumeRadius_linearIsometryImage,
    convexBodySphericalMeanWidth_linearIsometryImage,
    IntrinsicCoordinates.sphericalMeanWidth_coordinateBody,
    convexBodyNormalizedVolumeRadius,
    IntrinsicCoordinates.volumeReal_coordinateBody P hdim,
    finrank_directionSpan_eq_dim] at hU
  exact hU

/-- Equivalent half-mean-width form of intrinsic Urysohn. -/
theorem intrinsicVolumeRadius_le_half_intrinsicMeanWidth
    (P : IntrinsicBody E) [Nontrivial P.directionSpan] (hdim : P.dim ≠ 0)
    (hBM : ∀ K L : ConvexBody
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ P.directionSpan))),
      BrunnMinkowskiAt (1 / 2 : ℝ) K L) :
    (P.volumeReal / kappaReal P.dim) ^ ((P.dim : ℝ)⁻¹) ≤
      intrinsicMeanWidth P P.directionSpan / 2 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using
    two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth P hdim hBM

end IntrinsicBody

end ZeroOrderBounds.AccuracyImprovement
