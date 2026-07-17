import FullDMinusOneHalfAccuracy.MinkowskiWidth
import FullDMinusOneHalfAccuracy.OrthogonalHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Orthogonal matrices acting on Euclidean convex bodies

This file connects the compact matrix orthogonal group from
`OrthogonalHaar` to Mathlib's `LinearIsometryEquiv` API.  It also bundles the
image action on convex bodies and proves exact preservation of width and
Euclidean volume.
-/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix

namespace ZeroOrderBounds.AccuracyImprovement

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Matrix multiplication by an orthogonal matrix, as a linear equivalence of
Euclidean coordinate space. -/
def orthogonalLinearEquiv (A : Matrix.orthogonalGroup n ℝ) :
    EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n where
  toFun x := WithLp.toLp 2 (Matrix.UnitaryGroup.toLinearEquiv A x.ofLp)
  invFun x := WithLp.toLp 2
    ((Matrix.UnitaryGroup.toLinearEquiv A).symm x.ofLp)
  left_inv x := by
    apply WithLp.ofLp_injective
    simp
  right_inv x := by
    apply WithLp.ofLp_injective
    simp
  map_add' x y := by
    apply WithLp.ofLp_injective
    simp
  map_smul' c x := by
    apply WithLp.ofLp_injective
    simp

/-- Orthogonal matrix multiplication preserves the Euclidean inner product. -/
theorem orthogonalLinearEquiv_inner (A : Matrix.orthogonalGroup n ℝ)
    (x y : EuclideanSpace ℝ n) :
    inner ℝ (orthogonalLinearEquiv A x) (orthogonalLinearEquiv A y) =
      inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (A.1 *ᵥ y.ofLp) ⬝ᵥ star (A.1 *ᵥ x.ofLp) =
    y.ofLp ⬝ᵥ star x.ofLp
  simp only [Matrix.star_mulVec]
  rw [dotProduct_comm]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  have hA : (A.1)ᴴ * A.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self A
  rw [hA]
  rw [Matrix.vecMul_one]
  rw [dotProduct_comm]

theorem orthogonalLinearEquiv_norm (A : Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖orthogonalLinearEquiv A x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact orthogonalLinearEquiv_inner A x x

/-- Matrix multiplication by an orthogonal matrix, as a Euclidean linear
isometry equivalence. -/
def orthogonalLinearIsometryEquiv (A : Matrix.orthogonalGroup n ℝ) :
    EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n where
  toLinearEquiv := orthogonalLinearEquiv A
  norm_map' := orthogonalLinearEquiv_norm A

/-- Image of a convex body under a Euclidean linear isometry equivalence. -/
def convexBodyLinearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := e '' (K : Set E)
  convex' := K.convex.linear_image e.toLinearMap
  isCompact' := K.isCompact.image e.continuous
  nonempty' := K.nonempty.image e

@[simp]
theorem coe_convexBodyLinearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    (convexBodyLinearIsometryImage e K : Set F) = e '' (K : Set E) :=
  rfl

/-- Width of an isometric image is width in the pulled-back direction. -/
theorem directionalWidth_convexBodyLinearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) (theta : F) :
    directionalWidth (convexBodyLinearIsometryImage e K : Set F) theta =
      directionalWidth (K : Set E) (e.symm theta) := by
  exact directionalWidth_linearIsometryEquiv_image
    K.isCompact K.nonempty e theta

/-- Euclidean volume is invariant under a linear isometry equivalence. -/
theorem volume_convexBodyLinearIsometryImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) :
    volume (convexBodyLinearIsometryImage e K : Set F) =
      volume (K : Set E) := by
  have hpre : e.symm ⁻¹' (K : Set E) = e '' (K : Set E) := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [coe_convexBodyLinearIsometryImage, ← hpre]
  exact (LinearIsometryEquiv.measurePreserving e.symm).measure_preimage_equiv
    (f := e.symm.toHomeomorph.toMeasurableEquiv) (K : Set E)

/-- Rotation of a Euclidean convex body by an orthogonal matrix. -/
def orthogonalRotate (A : Matrix.orthogonalGroup n ℝ)
    (K : ConvexBody (EuclideanSpace ℝ n)) :
    ConvexBody (EuclideanSpace ℝ n) :=
  convexBodyLinearIsometryImage (orthogonalLinearIsometryEquiv A) K

@[simp]
theorem volume_orthogonalRotate (A : Matrix.orthogonalGroup n ℝ)
    (K : ConvexBody (EuclideanSpace ℝ n)) :
    volume (orthogonalRotate A K : Set (EuclideanSpace ℝ n)) =
      volume (K : Set (EuclideanSpace ℝ n)) :=
  volume_convexBodyLinearIsometryImage (orthogonalLinearIsometryEquiv A) K

end ZeroOrderBounds.AccuracyImprovement
