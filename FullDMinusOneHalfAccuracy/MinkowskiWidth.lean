import FullDMinusOneHalfAccuracy.DirectionalWidth
import FullDMinusOneHalfAccuracy.SphereMeasure
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Directional width and Minkowski operations

This file records the algebraic part of the convex-geometric averaging
argument behind Urysohn's inequality.  In particular, full directional width
is additive under Minkowski addition, homogeneous under dilation, and natural
under Euclidean linear isometries.  These facts are proved directly from
compact extrema, independently of any Brunn--Minkowski inequality.

Keeping these lemmas separate is useful for the eventual rotation-average
proof: Brunn--Minkowski is the only genuinely volumetric ingredient, whereas
all support-function bookkeeping lives here.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped Pointwise

namespace ZeroOrderBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If specified points maximize and minimize a linear functional on a
compact nonempty set, their support difference is its directional width. -/
theorem directionalWidth_eq_inner_sub_of_extrema {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) (theta p q : E)
    (hp : p ∈ s) (hq : q ∈ s)
    (hpmax : ∀ x ∈ s, inner ℝ theta x ≤ inner ℝ theta p)
    (hqmin : ∀ x ∈ s, inner ℝ theta q ≤ inner ℝ theta x) :
    directionalWidth s theta = inner ℝ theta p - inner ℝ theta q := by
  obtain ⟨p', hp', q', hq', hp'max, hq'min, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq hs hne theta
  rw [hwidth]
  exact le_antisymm (sub_le_sub (hpmax p' hp') (hqmin q' hq'))
    (sub_le_sub (hp'max p hp) (hq'min q hq))

/-- Full width is additive under Minkowski addition of compact nonempty
sets. -/
theorem directionalWidth_add {s t : Set E}
    (hs : IsCompact s) (hneS : s.Nonempty)
    (ht : IsCompact t) (hneT : t.Nonempty) (theta : E) :
    directionalWidth (s + t) theta =
      directionalWidth s theta + directionalWidth t theta := by
  obtain ⟨ps, hps, qs, hqs, hpsmax, hqsmin, hws⟩ :=
    IsCompact.exists_directionalWidth_eq hs hneS theta
  obtain ⟨pt, hpt, qt, hqt, hptmax, hqtmin, hwt⟩ :=
    IsCompact.exists_directionalWidth_eq ht hneT theta
  have hpadd : ps + pt ∈ s + t := Set.mem_add.mpr ⟨ps, hps, pt, hpt, rfl⟩
  have hqadd : qs + qt ∈ s + t := Set.mem_add.mpr ⟨qs, hqs, qt, hqt, rfl⟩
  have hpmax : ∀ x ∈ s + t,
      inner ℝ theta x ≤ inner ℝ theta (ps + pt) := by
    intro x hx
    obtain ⟨xs, hxs, xt, hxt, rfl⟩ := Set.mem_add.mp hx
    simp only [inner_add_right]
    exact add_le_add (hpsmax xs hxs) (hptmax xt hxt)
  have hqmin : ∀ x ∈ s + t,
      inner ℝ theta (qs + qt) ≤ inner ℝ theta x := by
    intro x hx
    obtain ⟨xs, hxs, xt, hxt, rfl⟩ := Set.mem_add.mp hx
    simp only [inner_add_right]
    exact add_le_add (hqsmin xs hxs) (hqtmin xt hxt)
  rw [directionalWidth_eq_inner_sub_of_extrema (hs.add ht)
      (hneS.add hneT) theta (ps + pt) (qs + qt) hpadd hqadd hpmax hqmin,
    hws, hwt]
  simp only [inner_add_right]
  ring

/-- Dilating a compact nonempty set by a nonnegative scalar dilates every
full width by the same scalar. -/
theorem directionalWidth_smul_set_of_nonneg {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) (theta : E)
    {c : ℝ} (hc : 0 ≤ c) :
    directionalWidth (c • s) theta = c * directionalWidth s theta := by
  obtain ⟨p, hp, q, hq, hpmax, hqmin, hw⟩ :=
    IsCompact.exists_directionalWidth_eq hs hne theta
  have hcp : c • p ∈ c • s := Set.mem_smul_set.mpr ⟨p, hp, rfl⟩
  have hcq : c • q ∈ c • s := Set.mem_smul_set.mpr ⟨q, hq, rfl⟩
  have hmax : ∀ x ∈ c • s,
      inner ℝ theta x ≤ inner ℝ theta (c • p) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp only [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hpmax y hy) hc
  have hmin : ∀ x ∈ c • s,
      inner ℝ theta (c • q) ≤ inner ℝ theta x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp only [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hqmin y hy) hc
  rw [directionalWidth_eq_inner_sub_of_extrema (hs.smul c)
      hne.smul_set theta (c • p) (c • q) hcp hcq hmax hmin, hw]
  simp only [real_inner_smul_right]
  ring

/-- The cross-space form of chord-preserving naturality. -/
theorem directionalWidth_image_eq_of_inner_sub_eq_cross
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E → F) (hf : ContinuousOn f s) {theta : F} {phi : E}
    (hinner : ∀ x ∈ s, ∀ y ∈ s,
      inner ℝ theta (f x - f y) = inner ℝ phi (x - y)) :
    directionalWidth (f '' s) theta = directionalWidth s phi := by
  have himage : IsCompact (f '' s) := hs.image_of_continuousOn hf
  have hneimage : (f '' s).Nonempty := hne.image f
  apply le_antisymm
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq himage hneimage theta
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    rw [hwidth, ← inner_sub_right, hinner x hx y hy]
    exact inner_sub_le_directionalWidth hs hne phi hx hy
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne phi
    rw [hwidth, ← inner_sub_right, ← hinner p hp q hq]
    exact inner_sub_le_directionalWidth himage hneimage theta
      (mem_image_of_mem f hp) (mem_image_of_mem f hq)

/-- Directional width is natural under a Euclidean linear-isometry
equivalence. -/
theorem directionalWidth_linearIsometryEquiv_image
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (e : E ≃ₗᵢ[ℝ] F) (theta : F) :
    directionalWidth (e '' s) theta = directionalWidth s (e.symm theta) := by
  apply directionalWidth_image_eq_of_inner_sub_eq_cross hs hne e
    e.continuous.continuousOn
  intro x hx y hy
  calc
    inner ℝ theta (e x - e y) = inner ℝ theta (e (x - y)) := by
      rw [e.map_sub]
    _ = inner ℝ (e (x - y)) theta := real_inner_comm _ _
    _ = inner ℝ (x - y) (e.symm theta) :=
      e.inner_map_eq_flip (x - y) theta
    _ = inner ℝ (e.symm theta) (x - y) := real_inner_comm _ _

/-! ## Bundled convex bodies -/

namespace ConvexBody

theorem directionalWidth_add (K L : ConvexBody E) (theta : E) :
    ZeroOrderBounds.directionalWidth (K + L : Set E) theta =
      ZeroOrderBounds.directionalWidth (K : Set E) theta +
        ZeroOrderBounds.directionalWidth (L : Set E) theta := by
  exact ZeroOrderBounds.directionalWidth_add K.isCompact K.nonempty
    L.isCompact L.nonempty theta

theorem directionalWidth_smul_of_nonneg (K : ConvexBody E) (theta : E)
    {c : ℝ} (hc : 0 ≤ c) :
    ZeroOrderBounds.directionalWidth (c • K : Set E) theta =
      c * ZeroOrderBounds.directionalWidth (K : Set E) theta := by
  exact ZeroOrderBounds.directionalWidth_smul_set_of_nonneg
    K.isCompact K.nonempty theta hc

end ConvexBody

end ZeroOrderBounds

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Spherical mean of the full width of a bundled convex body.  This is the
full-dimensional version of `intrinsicMeanWidth` used later for affine row
bodies. -/
def convexBodySphericalMeanWidth [Nontrivial E] (K : ConvexBody E) : ℝ :=
  ∫ u : UnitSphere E, directionalWidth (K : Set E) (u : E)
    ∂(sphereProbability E : Measure (UnitSphere E))

theorem integrable_convexBodySphereWidth [Nontrivial E]
    (K : ConvexBody E) :
    Integrable (fun u : UnitSphere E ↦ directionalWidth (K : Set E) (u : E))
      (sphereProbability E : Measure (UnitSphere E)) := by
  apply Continuous.integrable_sphereProbability (E := E)
  exact (continuous_directionalWidth K.isCompact).comp continuous_subtype_val

/-- Spherical mean width is nonnegative. -/
theorem ConvexBody.sphericalMeanWidth_nonneg [Nontrivial E]
    (K : ConvexBody E) : 0 ≤ convexBodySphericalMeanWidth K := by
  apply integral_nonneg
  intro u
  exact directionalWidth_nonneg K.isCompact K.nonempty (u : E)

/-- Spherical mean width is additive under Minkowski addition. -/
theorem ConvexBody.sphericalMeanWidth_add [Nontrivial E]
    (K L : ConvexBody E) :
    convexBodySphericalMeanWidth (K + L) =
      convexBodySphericalMeanWidth K + convexBodySphericalMeanWidth L := by
  rw [convexBodySphericalMeanWidth, convexBodySphericalMeanWidth,
    convexBodySphericalMeanWidth, ← integral_add
      (integrable_convexBodySphereWidth K)
      (integrable_convexBodySphereWidth L)]
  apply integral_congr_ae
  filter_upwards [] with u
  exact ZeroOrderBounds.ConvexBody.directionalWidth_add K L (u : E)

/-- Spherical mean width is homogeneous under nonnegative dilation. -/
theorem ConvexBody.sphericalMeanWidth_smul_of_nonneg [Nontrivial E]
    (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) :
    convexBodySphericalMeanWidth (c • K) = c * convexBodySphericalMeanWidth K := by
  rw [convexBodySphericalMeanWidth, convexBodySphericalMeanWidth,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  exact ZeroOrderBounds.ConvexBody.directionalWidth_smul_of_nonneg K (u : E) hc

end ZeroOrderBounds.AccuracyImprovement
