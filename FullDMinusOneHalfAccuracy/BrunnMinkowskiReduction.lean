import FullDMinusOneHalfAccuracy.BrunnMinkowski

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Reduction of Brunn--Minkowski to the equal-volume case

The slice/transport proof naturally gives Brunn--Minkowski first for two
bodies having the same positive volume.  This file proves, with no geometric
assumptions beyond that equal-volume theorem, the standard normalization
argument which gives the result for arbitrary *positive-volume* bodies.

Keeping this reduction separate is useful for auditability: all division and
all changes of interpolation weight are visible here, while the slice proof
only has to establish its normalized conclusion.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Point bodies, translations, and monotonicity -/

/-- A singleton packaged as a convex body. -/
def pointConvexBody (x : E) : ConvexBody E where
  carrier := {x}
  convex' := convex_singleton x
  isCompact' := isCompact_singleton
  nonempty' := singleton_nonempty x

@[simp]
theorem coe_pointConvexBody (x : E) :
    (pointConvexBody x : Set E) = {x} :=
  rfl

theorem pointConvexBody_le {K : ConvexBody E} {x : E} (hx : x ∈ K) :
    pointConvexBody x ≤ K := by
  intro y hy
  simpa only [coe_pointConvexBody, mem_singleton_iff] using hy ▸ hx

@[simp]
theorem smul_pointConvexBody (c : ℝ) (x : E) :
    c • pointConvexBody x = pointConvexBody (c • x) := by
  apply ConvexBody.ext
  simp only [ConvexBody.coe_smul, coe_pointConvexBody, smul_set_singleton]

/-- Translation by a point body preserves real Euclidean volume. -/
theorem convexBodyVolumeReal_point_add (x : E) (K : ConvexBody E) :
    convexBodyVolumeReal (pointConvexBody x + K) =
      convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal, ConvexBody.coe_add,
    coe_pointConvexBody, singleton_add, Set.image_add_left,
    measure_preimage_add]

/-- Translation by a point body preserves the homogeneous volume root. -/
theorem convexBodyVolumeRoot_point_add (x : E) (K : ConvexBody E) :
    convexBodyVolumeRoot (pointConvexBody x + K) =
      convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_point_add]

theorem convexBodyVolumeRoot_add_point (K : ConvexBody E) (x : E) :
    convexBodyVolumeRoot (K + pointConvexBody x) =
      convexBodyVolumeRoot K := by
  rw [add_comm, convexBodyVolumeRoot_point_add]

/-- Inclusion monotonicity, kept local to the normalization/degenerate-case
module so it does not introduce a dependency on the slice development. -/
theorem convexBodyVolumeRoot_mono_of_subset_reduction
    {A B : ConvexBody E} (hAB : (A : Set E) ⊆ (B : Set E)) :
    convexBodyVolumeRoot A ≤ convexBodyVolumeRoot B := by
  apply Real.rpow_le_rpow (convexBodyVolumeReal_nonneg A) _
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply (ENNReal.toReal_le_toReal A.isCompact.measure_lt_top.ne
    B.isCompact.measure_lt_top.ne).2
  exact measure_mono hAB

/-- The weight which appears after normalizing two positive volume roots to
one.  If `a` and `b` are the original roots, the common dilation after the
normalized interpolation is `(1-t)*a+t*b`. -/
def normalizedInterpolationWeight (t a b : ℝ) : ℝ :=
  t * b / ((1 - t) * a + t * b)

theorem normalizedInterpolationWeight_nonneg
    {t a b : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ normalizedInterpolationWeight t a b := by
  apply div_nonneg
  · exact mul_nonneg ht₀ hb.le
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht₁) ha.le)
      (mul_nonneg ht₀ hb.le)

theorem normalizedInterpolationWeight_le_one
    {t a b : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) :
    normalizedInterpolationWeight t a b ≤ 1 := by
  have hc : 0 < (1 - t) * a + t * b := by
    rcases eq_or_lt_of_le ht₀ with rfl | ht
    · simpa using ha
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht₁) ha.le) (mul_pos ht hb)
  rw [normalizedInterpolationWeight, div_le_one hc]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) ha.le]

/-- Exact body identity underlying the normalization argument. -/
theorem normalized_weightedMinkowski_identity
    (K L : ConvexBody E) {t a b : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    ((1 - t) * a + t * b) •
        weightedMinkowski (normalizedInterpolationWeight t a b)
          (a⁻¹ • K) (b⁻¹ • L) =
      weightedMinkowski t K L := by
  let c : ℝ := (1 - t) * a + t * b
  have hc : 0 < c := by
    rcases eq_or_lt_of_le ht₀ with rfl | ht
    · simpa [c] using ha
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht₁) ha.le) (mul_pos ht hb)
  have hK : c * (1 - normalizedInterpolationWeight t a b) * a⁻¹ = 1 - t := by
    rw [normalizedInterpolationWeight]
    dsimp only [c] at hc ⊢
    field_simp [ha.ne', hb.ne', hc.ne']
    ring
  have hL : c * normalizedInterpolationWeight t a b * b⁻¹ = t := by
    rw [normalizedInterpolationWeight]
    dsimp only [c] at hc ⊢
    field_simp [ha.ne', hb.ne', hc.ne']
  rw [weightedMinkowski, weightedMinkowski, smul_add, smul_smul,
    smul_smul, smul_smul, smul_smul, hK, hL]

/-! ## Degenerate-volume cases -/

theorem convexBodyVolumeRoot_weighted_point_left
    (hdim : Module.finrank ℝ E ≠ 0) (x : E) (L : ConvexBody E)
    {t : ℝ} (ht₀ : 0 ≤ t) :
    convexBodyVolumeRoot (weightedMinkowski t (pointConvexBody x) L) =
      t * convexBodyVolumeRoot L := by
  rw [weightedMinkowski, smul_pointConvexBody,
    convexBodyVolumeRoot_point_add,
    convexBodyVolumeRoot_smul_of_nonneg L hdim ht₀]

theorem convexBodyVolumeRoot_weighted_point_right
    (hdim : Module.finrank ℝ E ≠ 0) (K : ConvexBody E) (x : E)
    {t : ℝ} (ht₁ : t ≤ 1) :
    convexBodyVolumeRoot (weightedMinkowski t K (pointConvexBody x)) =
      (1 - t) * convexBodyVolumeRoot K := by
  rw [weightedMinkowski, smul_pointConvexBody,
    convexBodyVolumeRoot_add_point,
    convexBodyVolumeRoot_smul_of_nonneg K hdim (sub_nonneg.mpr ht₁)]

/-- If the left body has zero volume root, a translated copy of `t • L`
inside the weighted sum proves Brunn--Minkowski directly. -/
theorem brunnMinkowskiAt_of_left_root_eq_zero
    (hdim : Module.finrank ℝ E ≠ 0)
    (K L : ConvexBody E) {t : ℝ}
    (ht₀ : 0 ≤ t) (hKzero : convexBodyVolumeRoot K = 0) :
    BrunnMinkowskiAt t K L := by
  obtain ⟨x, hx⟩ := K.nonempty
  have hsub :
      (weightedMinkowski t (pointConvexBody x) L : Set E) ⊆
        (weightedMinkowski t K L : Set E) := by
    simp only [weightedMinkowski, ConvexBody.coe_add, ConvexBody.coe_smul]
    exact Set.add_subset_add
      (Set.smul_set_mono (show (pointConvexBody x : Set E) ⊆ K from
        pointConvexBody_le hx)) Subset.rfl
  have hmono := convexBodyVolumeRoot_mono_of_subset_reduction hsub
  rw [convexBodyVolumeRoot_weighted_point_left hdim x L ht₀] at hmono
  rw [BrunnMinkowskiAt, hKzero, mul_zero, zero_add]
  exact hmono

/-- Symmetric degenerate case when the right body has zero volume root. -/
theorem brunnMinkowskiAt_of_right_root_eq_zero
    (hdim : Module.finrank ℝ E ≠ 0)
    (K L : ConvexBody E) {t : ℝ}
    (ht₁ : t ≤ 1) (hLzero : convexBodyVolumeRoot L = 0) :
    BrunnMinkowskiAt t K L := by
  obtain ⟨y, hy⟩ := L.nonempty
  have hsub :
      (weightedMinkowski t K (pointConvexBody y) : Set E) ⊆
        (weightedMinkowski t K L : Set E) := by
    simp only [weightedMinkowski, ConvexBody.coe_add, ConvexBody.coe_smul]
    exact Set.add_subset_add Subset.rfl
      (Set.smul_set_mono (show (pointConvexBody y : Set E) ⊆ L from
        pointConvexBody_le hy))
  have hmono := convexBodyVolumeRoot_mono_of_subset_reduction hsub
  rw [convexBodyVolumeRoot_weighted_point_right hdim K y ht₁] at hmono
  rw [BrunnMinkowskiAt, hLzero, mul_zero, add_zero]
  exact hmono

/-- Positive-volume Brunn--Minkowski follows from its equal-volume case.

The premise `hEqual` is deliberately an ordinary theorem argument rather
than an axiom or a typeclass field.  The slice/quantile induction can supply
it directly. -/
theorem brunnMinkowskiAt_of_pos_of_equal_volume
    (hdim : Module.finrank ℝ E ≠ 0)
    (hEqual : ∀ (s : ℝ) (A B : ConvexBody E),
      0 ≤ s → s ≤ 1 →
      convexBodyVolumeRoot A = convexBodyVolumeRoot B →
      BrunnMinkowskiAt s A B)
    (K L : ConvexBody E) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hK : 0 < convexBodyVolumeRoot K)
    (hL : 0 < convexBodyVolumeRoot L) :
    BrunnMinkowskiAt t K L := by
  let a : ℝ := convexBodyVolumeRoot K
  let b : ℝ := convexBodyVolumeRoot L
  let c : ℝ := (1 - t) * a + t * b
  let s : ℝ := normalizedInterpolationWeight t a b
  have ha : 0 < a := hK
  have hb : 0 < b := hL
  have hc : 0 < c := by
    rcases eq_or_lt_of_le ht₀ with rfl | ht
    · simpa [c] using ha
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht₁) ha.le) (mul_pos ht hb)
  have hs₀ : 0 ≤ s :=
    normalizedInterpolationWeight_nonneg ht₀ ht₁ ha hb
  have hs₁ : s ≤ 1 :=
    normalizedInterpolationWeight_le_one ht₀ ht₁ ha hb
  have haInv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hbInv : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hrootK : convexBodyVolumeRoot (a⁻¹ • K) = 1 := by
    rw [convexBodyVolumeRoot_smul_of_nonneg K hdim haInv]
    dsimp only [a]
    exact inv_mul_cancel₀ ha.ne'
  have hrootL : convexBodyVolumeRoot (b⁻¹ • L) = 1 := by
    rw [convexBodyVolumeRoot_smul_of_nonneg L hdim hbInv]
    dsimp only [b]
    exact inv_mul_cancel₀ hb.ne'
  have hnormalized : BrunnMinkowskiAt s (a⁻¹ • K) (b⁻¹ • L) :=
    hEqual s (a⁻¹ • K) (b⁻¹ • L) hs₀ hs₁ (hrootK.trans hrootL.symm)
  have hscaled :
      c ≤ convexBodyVolumeRoot
        (c • weightedMinkowski s (a⁻¹ • K) (b⁻¹ • L)) := by
    rw [convexBodyVolumeRoot_smul_of_nonneg _ hdim hc.le]
    rw [BrunnMinkowskiAt] at hnormalized
    rw [hrootK, hrootL] at hnormalized
    have hone : (1 - s) * 1 + s * 1 = 1 := by ring
    rw [hone] at hnormalized
    nlinarith [hc]
  rw [normalized_weightedMinkowski_identity K L ht₀ ht₁ ha hb] at hscaled
  simpa [BrunnMinkowskiAt, a, b, c] using hscaled

/-- The equal-volume case, together with the elementary translated-dilate
argument for zero-volume bodies, implies full Brunn--Minkowski for all
convex bodies. -/
theorem brunnMinkowskiAt_of_equal_volume_case
    (hdim : Module.finrank ℝ E ≠ 0)
    (hEqual : ∀ (s : ℝ) (A B : ConvexBody E),
      0 ≤ s → s ≤ 1 →
      convexBodyVolumeRoot A = convexBodyVolumeRoot B →
      BrunnMinkowskiAt s A B)
    (K L : ConvexBody E) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K L := by
  by_cases hKzero : convexBodyVolumeRoot K = 0
  · exact brunnMinkowskiAt_of_left_root_eq_zero hdim K L ht₀ hKzero
  by_cases hLzero : convexBodyVolumeRoot L = 0
  · exact brunnMinkowskiAt_of_right_root_eq_zero hdim K L ht₁ hLzero
  exact brunnMinkowskiAt_of_pos_of_equal_volume hdim hEqual K L ht₀ ht₁
    (lt_of_le_of_ne (convexBodyVolumeRoot_nonneg K) (Ne.symm hKzero))
    (lt_of_le_of_ne (convexBodyVolumeRoot_nonneg L) (Ne.symm hLzero))

end ZeroOrderBounds.AccuracyImprovement
