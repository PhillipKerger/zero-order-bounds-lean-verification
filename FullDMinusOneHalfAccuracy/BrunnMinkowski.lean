import FullDMinusOneHalfAccuracy.MinkowskiWidth
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Brunn--Minkowski vocabulary and verified special cases

This module fixes the exact real-valued formulation of Brunn--Minkowski used
by the Urysohn proof.  It also proves all scalar bookkeeping and the theorem
for homothetic convex bodies.  The remaining general case is a genuine
convex-geometric theorem, not an assumption or a typeclass field; no
declaration in this file asserts it without proof.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Real Euclidean volume of a compact convex body. -/
def convexBodyVolumeReal (K : ConvexBody E) : ℝ :=
  (volume (K : Set E)).toReal

theorem convexBodyVolumeReal_nonneg (K : ConvexBody E) :
    0 ≤ convexBodyVolumeReal K :=
  ENNReal.toReal_nonneg

/-- The homogeneous `dim`-th root of Euclidean volume. -/
def convexBodyVolumeRoot (K : ConvexBody E) : ℝ :=
  convexBodyVolumeReal K ^ ((Module.finrank ℝ E : ℝ)⁻¹)

theorem convexBodyVolumeRoot_nonneg (K : ConvexBody E) :
    0 ≤ convexBodyVolumeRoot K :=
  Real.rpow_nonneg (convexBodyVolumeReal_nonneg K) _

/-- Minkowski interpolation between two bodies. -/
def weightedMinkowski (t : ℝ) (K L : ConvexBody E) : ConvexBody E :=
  (1 - t) • K + t • L

/-- The exact Brunn--Minkowski conclusion at a weight `t`. -/
def BrunnMinkowskiAt (t : ℝ) (K L : ConvexBody E) : Prop :=
  (1 - t) * convexBodyVolumeRoot K + t * convexBodyVolumeRoot L ≤
    convexBodyVolumeRoot (weightedMinkowski t K L)

/-- Dilation by a nonnegative scalar scales real volume by `c^dim`. -/
theorem convexBodyVolumeReal_smul_of_nonneg (K : ConvexBody E)
    {c : ℝ} (hc : 0 ≤ c) :
    convexBodyVolumeReal (c • K) =
      c ^ Module.finrank ℝ E * convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal, ConvexBody.coe_smul,
    Measure.addHaar_smul_of_nonneg volume hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc _)]

/-- In positive dimension, the volume root is exactly one-homogeneous. -/
theorem convexBodyVolumeRoot_smul_of_nonneg (K : ConvexBody E)
    (hdim : Module.finrank ℝ E ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    convexBodyVolumeRoot (c • K) = c * convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_smul_of_nonneg K hc]
  rw [Real.mul_rpow (pow_nonneg hc _) (convexBodyVolumeReal_nonneg K)]
  rw [Real.pow_rpow_inv_natCast hc hdim]

/-- A weighted Minkowski sum of a body and a nonnegative homothetic copy is
the corresponding homothetic copy. -/
theorem weightedMinkowski_smul_eq (K : ConvexBody E)
    {t c : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hc : 0 ≤ c) :
    weightedMinkowski t K (c • K) = ((1 - t) + t * c) • K := by
  apply ConvexBody.ext
  simp only [weightedMinkowski, ConvexBody.coe_add, ConvexBody.coe_smul,
    smul_smul]
  rw [K.convex.add_smul (sub_nonneg.mpr ht₁) (mul_nonneg ht₀ hc)]

/-- Brunn--Minkowski holds with equality for nonnegative homothetic bodies.
This verifies the normalization and scalar orientation of
`BrunnMinkowskiAt`. -/
theorem brunnMinkowskiAt_smul (K : ConvexBody E)
    (hdim : Module.finrank ℝ E ≠ 0)
    {t c : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hc : 0 ≤ c) :
    BrunnMinkowskiAt t K (c • K) := by
  rw [BrunnMinkowskiAt, weightedMinkowski_smul_eq K ht₀ ht₁ hc,
    convexBodyVolumeRoot_smul_of_nonneg K hdim hc,
    convexBodyVolumeRoot_smul_of_nonneg K hdim
      (add_nonneg (sub_nonneg.mpr ht₁) (mul_nonneg ht₀ hc))]
  ring_nf
  exact le_rfl

/-- Reflexive interpolation is the `c=1` instance of the homothetic theorem. -/
theorem brunnMinkowskiAt_self (K : ConvexBody E)
    (hdim : Module.finrank ℝ E ≠ 0)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K K := by
  simpa using brunnMinkowskiAt_smul K hdim ht₀ ht₁
    (c := 1) zero_le_one

/-- Width is affine along Minkowski interpolation. -/
theorem directionalWidth_weightedMinkowski (K L : ConvexBody E)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (theta : E) :
    directionalWidth (weightedMinkowski t K L : Set E) theta =
      (1 - t) * directionalWidth (K : Set E) theta +
        t * directionalWidth (L : Set E) theta := by
  rw [weightedMinkowski, ConvexBody.coe_add,
    ConvexBody.coe_smul, ConvexBody.coe_smul,
    ZeroOrderBounds.directionalWidth_add
      (K.isCompact.smul (1 - t)) K.nonempty.smul_set
      (L.isCompact.smul t) L.nonempty.smul_set,
    ZeroOrderBounds.directionalWidth_smul_set_of_nonneg
      K.isCompact K.nonempty theta (sub_nonneg.mpr ht₁),
    ZeroOrderBounds.directionalWidth_smul_set_of_nonneg
      L.isCompact L.nonempty theta ht₀]

/-! ## The complete one-dimensional theorem -/

/-- A compact convex body in `ℝ` is the interval between its support
extrema, so its real volume is its full width. -/
theorem convexBodyVolumeReal_real_eq_directionalWidth (K : ConvexBody ℝ) :
    convexBodyVolumeReal K = directionalWidth (K : Set ℝ) 1 := by
  obtain ⟨p, hp, q, hq, hpmax, hqmin, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq K.isCompact K.nonempty (1 : ℝ)
  have hpmax' : ∀ x ∈ (K : Set ℝ), x ≤ p := by
    intro x hx
    simpa using hpmax x hx
  have hqmin' : ∀ x ∈ (K : Set ℝ), q ≤ x := by
    intro x hx
    simpa using hqmin x hx
  have hqp : q ≤ p := hqmin' p hp
  have hcarrier : (K : Set ℝ) = Set.Icc q p := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hqmin' x hx, hpmax' x hx⟩
    · exact K.convex.ordConnected.out hq hp
  calc
    convexBodyVolumeReal K = p - q := by
      rw [convexBodyVolumeReal, hcarrier, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hqp)]
    _ = directionalWidth (K : Set ℝ) 1 := by
      simpa using hwidth.symm

/-- Consequently the one-dimensional volume root is exactly full width. -/
theorem convexBodyVolumeRoot_real_eq_directionalWidth (K : ConvexBody ℝ) :
    convexBodyVolumeRoot K = directionalWidth (K : Set ℝ) 1 := by
  rw [convexBodyVolumeRoot, Module.finrank_self, Nat.cast_one, inv_one,
    Real.rpow_one, convexBodyVolumeReal_real_eq_directionalWidth]

/-- Full one-dimensional Brunn--Minkowski, with equality for all compact
convex bodies. -/
theorem brunnMinkowskiAt_real (K L : ConvexBody ℝ)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K L := by
  rw [BrunnMinkowskiAt,
    convexBodyVolumeRoot_real_eq_directionalWidth,
    convexBodyVolumeRoot_real_eq_directionalWidth,
    convexBodyVolumeRoot_real_eq_directionalWidth,
    directionalWidth_weightedMinkowski K L ht₀ ht₁]

end ZeroOrderBounds.AccuracyImprovement
