import ZeroOrderBounds.IntrinsicVolume
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Directional width of a compact set

This file develops the elementary support-extrema API used by the improved-accuracy branch.
-/

noncomputable section

open scoped Pointwise
open MeasureTheory Metric Set

namespace ZeroOrderBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The maximum value of the linear functional in direction `θ` on `s`. -/
def directionalSupportSup (s : Set E) (θ : E) : ℝ :=
  sSup ((fun x : E ↦ inner ℝ θ x) '' s)

/-- The minimum value of the linear functional in direction `θ` on `s`. -/
def directionalSupportInf (s : Set E) (θ : E) : ℝ :=
  sInf ((fun x : E ↦ inner ℝ θ x) '' s)

/-- Full directional width: maximum support minus minimum support. -/
def directionalWidth (s : Set E) (θ : E) : ℝ :=
  directionalSupportSup s θ - directionalSupportInf s θ

theorem IsCompact.exists_directionalSupportSup_eq {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) :
    ∃ p ∈ s, directionalSupportSup s θ = inner ℝ θ p ∧
      ∀ x ∈ s, inner ℝ θ x ≤ inner ℝ θ p := by
  simpa [directionalSupportSup] using
    hs.exists_sSup_image_eq_and_ge hne
      (show ContinuousOn (fun x : E ↦ inner ℝ θ x) s by fun_prop)

theorem IsCompact.exists_directionalSupportInf_eq {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) :
    ∃ p ∈ s, directionalSupportInf s θ = inner ℝ θ p ∧
      ∀ x ∈ s, inner ℝ θ p ≤ inner ℝ θ x := by
  simpa [directionalSupportInf] using
    hs.exists_sInf_image_eq_and_le hne
      (show ContinuousOn (fun x : E ↦ inner ℝ θ x) s by fun_prop)

/-- A compact nonempty set has a pair of points realizing its full directional width. -/
theorem IsCompact.exists_directionalWidth_eq {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) :
    ∃ p ∈ s, ∃ q ∈ s,
      (∀ x ∈ s, inner ℝ θ x ≤ inner ℝ θ p) ∧
      (∀ x ∈ s, inner ℝ θ q ≤ inner ℝ θ x) ∧
      directionalWidth s θ = inner ℝ θ p - inner ℝ θ q := by
  obtain ⟨p, hp, hsup, hpmax⟩ :=
    IsCompact.exists_directionalSupportSup_eq hs hne θ
  obtain ⟨q, hq, hinf, hqmin⟩ :=
    IsCompact.exists_directionalSupportInf_eq hs hne θ
  exact ⟨p, hp, q, hq, hpmax, hqmin, by
    simp only [directionalWidth, hsup, hinf]⟩

/-- Every difference of two support values is bounded by the full directional width. -/
theorem inner_sub_inner_le_directionalWidth {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    inner ℝ θ x - inner ℝ θ y ≤ directionalWidth s θ := by
  obtain ⟨p, hp, q, hq, hpmax, hqmin, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq hs hne θ
  rw [hwidth]
  exact sub_le_sub (hpmax x hx) (hqmin y hy)

/-- The equivalent single-inner-product form of the pairwise width bound. -/
theorem inner_sub_le_directionalWidth {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    inner ℝ θ (x - y) ≤ directionalWidth s θ := by
  simpa [inner_sub_right] using
    inner_sub_inner_le_directionalWidth hs hne θ hx hy

/-- Directional width is nonnegative. -/
theorem directionalWidth_nonneg {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) : 0 ≤ directionalWidth s θ := by
  obtain ⟨p, hp, q, hq, hpmax, _hqmin, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq hs hne θ
  rw [hwidth]
  exact sub_nonneg.mpr (hpmax q hq)

/-- Widths agree when the two directions have the same inner product with every chord of `s`. -/
theorem directionalWidth_congr_of_inner_sub_eq {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) {θ φ : E}
    (hinner : ∀ x ∈ s, ∀ y ∈ s, inner ℝ θ (x - y) = inner ℝ φ (x - y)) :
    directionalWidth s θ = directionalWidth s φ := by
  apply le_antisymm
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne θ
    rw [hwidth, ← inner_sub_right, hinner p hp q hq]
    exact inner_sub_le_directionalWidth hs hne φ hp hq
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne φ
    rw [hwidth, ← inner_sub_right, ← hinner p hp q hq]
    exact inner_sub_le_directionalWidth hs hne θ hp hq

/-- A chord-preserving parametrization preserves directional width.  The directions in the
source and target spaces are allowed to differ; only their values on corresponding chords matter. -/
theorem directionalWidth_image_eq_of_inner_sub_eq {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (f : E → E) (hf : ContinuousOn f s) {θ φ : E}
    (hinner : ∀ x ∈ s, ∀ y ∈ s,
      inner ℝ θ (f x - f y) = inner ℝ φ (x - y)) :
    directionalWidth (f '' s) θ = directionalWidth s φ := by
  have himage : IsCompact (f '' s) := hs.image_of_continuousOn hf
  have hneimage : (f '' s).Nonempty := hne.image f
  apply le_antisymm
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq himage hneimage θ
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    rw [hwidth, ← inner_sub_right, hinner x hx y hy]
    exact inner_sub_le_directionalWidth hs hne φ hx hy
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne φ
    rw [hwidth, ← inner_sub_right, ← hinner p hp q hq, inner_sub_right]
    exact inner_sub_inner_le_directionalWidth himage hneimage θ
      (mem_image_of_mem f hp) (mem_image_of_mem f hq)

/-- Translation does not change directional width (image formulation). -/
theorem directionalWidth_translate_image {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (v θ : E) :
    directionalWidth ((fun x : E ↦ v + x) '' s) θ = directionalWidth s θ := by
  apply directionalWidth_image_eq_of_inner_sub_eq hs hne (fun x : E ↦ v + x)
    (by fun_prop)
  intro x hx y hy
  simp

/-- Translation does not change directional width (pointwise-action formulation). -/
theorem directionalWidth_vadd {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (v θ : E) :
    directionalWidth (v +ᵥ s) θ = directionalWidth s θ := by
  change directionalWidth ((fun x : E ↦ v + x) '' s) θ = directionalWidth s θ
  exact directionalWidth_translate_image hs hne v θ

/-- Directional width is positively homogeneous in the direction. -/
theorem directionalWidth_smul_of_nonneg {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) {c : ℝ} (hc : 0 ≤ c) :
    directionalWidth s (c • θ) = c * directionalWidth s θ := by
  apply le_antisymm
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne (c • θ)
    rw [hwidth]
    simp only [real_inner_smul_left]
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left
      (inner_sub_inner_le_directionalWidth hs hne θ hp hq) hc
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne θ
    rw [hwidth]
    calc
      c * (inner ℝ θ p - inner ℝ θ q) =
          inner ℝ (c • θ) p - inner ℝ (c • θ) q := by
            simp only [real_inner_smul_left, mul_sub]
      _ ≤ directionalWidth s (c • θ) :=
        inner_sub_inner_le_directionalWidth hs hne (c • θ) hp hq

/-- Reversing the direction leaves full width unchanged. -/
theorem directionalWidth_neg {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) : directionalWidth s (-θ) = directionalWidth s θ := by
  apply le_antisymm
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne (-θ)
    rw [hwidth]
    simp only [inner_neg_left]
    have h := inner_sub_inner_le_directionalWidth hs hne θ hq hp
    linarith
  · obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
      IsCompact.exists_directionalWidth_eq hs hne θ
    rw [hwidth]
    have h := inner_sub_inner_le_directionalWidth hs hne (-θ) hq hp
    simp only [inner_neg_left] at h
    linarith

/-- Full absolute homogeneity, derived from positive homogeneity and direction symmetry. -/
theorem directionalWidth_smul {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) (c : ℝ) :
    directionalWidth s (c • θ) = |c| * directionalWidth s θ := by
  rcases le_total 0 c with hc | hc
  · simpa [abs_of_nonneg hc] using directionalWidth_smul_of_nonneg hs hne θ hc
  · have hnc : 0 ≤ -c := neg_nonneg.mpr hc
    calc
      directionalWidth s (c • θ) = directionalWidth s ((-c) • (-θ)) := by
        rw [neg_smul, smul_neg, neg_neg]
      _ = (-c) * directionalWidth s (-θ) :=
        directionalWidth_smul_of_nonneg hs hne (-θ) hnc
      _ = |c| * directionalWidth s θ := by
        rw [directionalWidth_neg hs hne]
        simp [abs_of_nonpos hc]

@[simp]
theorem directionalWidth_zero {s : Set E} (hs : IsCompact s) (hne : s.Nonempty) :
    directionalWidth s (0 : E) = 0 := by
  simpa using directionalWidth_smul_of_nonneg hs hne (0 : E) (c := 0) le_rfl

/-- The upper support value varies continuously with direction. -/
theorem continuous_directionalSupportSup {s : Set E} (hs : IsCompact s) :
    Continuous (directionalSupportSup s) := by
  apply hs.continuous_sSup
  fun_prop

/-- The lower support value varies continuously with direction. -/
theorem continuous_directionalSupportInf {s : Set E} (hs : IsCompact s) :
    Continuous (directionalSupportInf s) := by
  apply hs.continuous_sInf
  fun_prop

/-- Directional width is a continuous function of the direction. -/
theorem continuous_directionalWidth {s : Set E} (hs : IsCompact s) :
    Continuous (directionalWidth s) := by
  exact (continuous_directionalSupportSup hs).sub (continuous_directionalSupportInf hs)

/-- Directional width is Borel measurable. -/
theorem measurable_directionalWidth [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : IsCompact s) :
    Measurable (directionalWidth s) :=
  (continuous_directionalWidth hs).measurable

/-- A width function is integrable on every compact set of directions for any locally finite
Borel measure.  This is the interface used for spherical integration. -/
theorem integrableOn_directionalWidth [MeasurableSpace E] [BorelSpace E]
    {s K : Set E} (hs : IsCompact s)
    (hK : IsCompact K) (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    IntegrableOn (directionalWidth s) K μ :=
  (continuous_directionalWidth hs).continuousOn.integrableOn_compact hK

/-- A compact body in a radius-`r` ball has width at most `2 r ‖θ‖`. -/
theorem directionalWidth_le_two_mul_norm {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) {r : ℝ} (hball : s ⊆ closedBall (0 : E) r) (θ : E) :
    directionalWidth s θ ≤ 2 * r * ‖θ‖ := by
  obtain ⟨p, hp, q, hq, _hpmax, _hqmin, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq hs hne θ
  have hpnorm : ‖p‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hball hp
  have hqnorm : ‖q‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hball hq
  calc
    directionalWidth s θ = inner ℝ θ (p - q) := by
      rw [hwidth, inner_sub_right]
    _ ≤ ‖θ‖ * ‖p - q‖ := real_inner_le_norm θ (p - q)
    _ ≤ ‖θ‖ * (‖p‖ + ‖q‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le p q) (norm_nonneg θ)
    _ ≤ ‖θ‖ * (r + r) :=
      mul_le_mul_of_nonneg_left (add_le_add hpnorm hqnorm) (norm_nonneg θ)
    _ = 2 * r * ‖θ‖ := by ring

/-- Absolute-value version of the radius bound. -/
theorem abs_directionalWidth_le_two_mul_norm {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) {r : ℝ} (hball : s ⊆ closedBall (0 : E) r) (θ : E) :
    |directionalWidth s θ| ≤ 2 * r * ‖θ‖ := by
  rw [abs_of_nonneg (directionalWidth_nonneg hs hne θ)]
  exact directionalWidth_le_two_mul_norm hs hne hball θ

/-- The linear subspace generated by all chords of a set.  For a nonempty set this is exactly
the usual `lin (s - s)`, represented canonically as the direction of its affine span. -/
def directionSpan (s : Set E) : Submodule ℝ E :=
  (affineSpan ℝ s).direction

/-- The chord-span representation is literally the linear span of the difference set `s - s`. -/
theorem directionSpan_eq_span_vsub (s : Set E) :
    directionSpan s = Submodule.span ℝ (s -ᵥ s) := by
  rw [directionSpan, direction_affineSpan, vectorSpan_def]

theorem sub_mem_directionSpan {s : Set E} {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    x - y ∈ directionSpan s := by
  exact (affineSpan ℝ s).vsub_mem_direction
    (subset_affineSpan ℝ s hx) (subset_affineSpan ℝ s hy)

/-- Width only sees the orthogonal projection of the direction onto the chord span. -/
theorem directionalWidth_starProjection_directionSpan [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (θ : E) :
    directionalWidth s ((directionSpan s).starProjection θ) = directionalWidth s θ := by
  apply directionalWidth_congr_of_inner_sub_eq hs hne
  intro x hx y hy
  have hxy : x - y ∈ directionSpan s := sub_mem_directionSpan hx hy
  have horth := (directionSpan s).starProjection_inner_eq_zero θ (x - y) hxy
  rw [inner_sub_left] at horth
  exact (sub_eq_zero.mp horth).symm

theorem directionalWidth_eq_starProjection_directionSpan [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) (hne : s.Nonempty) (θ : E) :
    directionalWidth s θ = directionalWidth s ((directionSpan s).starProjection θ) :=
  (directionalWidth_starProjection_directionSpan hs hne θ).symm

/-- Two directions with the same chord-span projection give the same width. -/
theorem directionalWidth_eq_of_starProjection_eq [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) (hne : s.Nonempty) {θ φ : E}
    (hproj : (directionSpan s).starProjection θ =
      (directionSpan s).starProjection φ) :
    directionalWidth s θ = directionalWidth s φ := by
  calc
    directionalWidth s θ =
        directionalWidth s ((directionSpan s).starProjection θ) :=
      directionalWidth_eq_starProjection_directionSpan hs hne θ
    _ = directionalWidth s ((directionSpan s).starProjection φ) := by rw [hproj]
    _ = directionalWidth s φ :=
      directionalWidth_starProjection_directionSpan hs hne φ

/-- More generally, directions differing by a vector orthogonal to every chord give the same
width. -/
theorem directionalWidth_eq_of_sub_mem_directionSpan_orthogonal {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) {θ φ : E}
    (horth : θ - φ ∈ (directionSpan s)ᗮ) :
    directionalWidth s θ = directionalWidth s φ := by
  apply directionalWidth_congr_of_inner_sub_eq hs hne
  intro x hx y hy
  have hxy : x - y ∈ directionSpan s := sub_mem_directionSpan hx hy
  have hz : inner ℝ (θ - φ) (x - y) = 0 := by
    simpa [real_inner_comm] using horth (x - y) hxy
  rw [inner_sub_left] at hz
  exact sub_eq_zero.mp hz

namespace IntrinsicBody

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Upper support of an intrinsic body. -/
def supportSup (P : IntrinsicBody E) (θ : E) : ℝ :=
  ZeroOrderBounds.directionalSupportSup P.carrier θ

/-- Lower support of an intrinsic body. -/
def supportInf (P : IntrinsicBody E) (θ : E) : ℝ :=
  ZeroOrderBounds.directionalSupportInf P.carrier θ

/-- Full directional width of an intrinsic body. -/
def directionalWidth (P : IntrinsicBody E) (θ : E) : ℝ :=
  ZeroOrderBounds.directionalWidth P.carrier θ

/-- The chord span of an intrinsic body. -/
def directionSpan (P : IntrinsicBody E) : Submodule ℝ E :=
  P.hull.direction

theorem directionSpan_eq_span_vsub (P : IntrinsicBody E) :
    P.directionSpan = Submodule.span ℝ (P.carrier -ᵥ P.carrier) := by
  rw [directionSpan, IntrinsicBody.hull, direction_affineSpan, vectorSpan_def]

/-- Translate an intrinsic body by an ambient vector. -/
def translate (P : IntrinsicBody E) (v : E) : IntrinsicBody E :=
  IntrinsicBody.ofCompactConvex ((fun x : E ↦ v + x) '' P.carrier)
    (P.nonempty.image _)
    (P.isCompact.image (by fun_prop))
    (P.convex.translate v)

@[simp]
theorem translate_carrier (P : IntrinsicBody E) (v : E) :
    (P.translate v).carrier = (fun x : E ↦ v + x) '' P.carrier :=
  rfl

@[simp]
theorem supportSup_eq (P : IntrinsicBody E) (θ : E) :
    P.supportSup θ = ZeroOrderBounds.directionalSupportSup P.carrier θ :=
  rfl

@[simp]
theorem supportInf_eq (P : IntrinsicBody E) (θ : E) :
    P.supportInf θ = ZeroOrderBounds.directionalSupportInf P.carrier θ :=
  rfl

@[simp]
theorem directionalWidth_eq (P : IntrinsicBody E) (θ : E) :
    P.directionalWidth θ = ZeroOrderBounds.directionalWidth P.carrier θ :=
  rfl

theorem directionalWidth_eq_supportSup_sub_supportInf (P : IntrinsicBody E) (θ : E) :
    P.directionalWidth θ = P.supportSup θ - P.supportInf θ :=
  rfl

theorem exists_supportSup_eq (P : IntrinsicBody E) (θ : E) :
    ∃ p ∈ P, P.supportSup θ = inner ℝ θ p ∧
      ∀ x ∈ P, inner ℝ θ x ≤ inner ℝ θ p := by
  simpa [supportSup] using
    IsCompact.exists_directionalSupportSup_eq P.isCompact P.nonempty θ

theorem exists_supportInf_eq (P : IntrinsicBody E) (θ : E) :
    ∃ p ∈ P, P.supportInf θ = inner ℝ θ p ∧
      ∀ x ∈ P, inner ℝ θ p ≤ inner ℝ θ x := by
  simpa [supportInf] using
    IsCompact.exists_directionalSupportInf_eq P.isCompact P.nonempty θ

/-- Audit-facing max/min witnesses realizing a body's directional width. -/
theorem exists_directionalWidth_eq (P : IntrinsicBody E) (θ : E) :
    ∃ p ∈ P, ∃ q ∈ P,
      (∀ x ∈ P, inner ℝ θ x ≤ inner ℝ θ p) ∧
      (∀ x ∈ P, inner ℝ θ q ≤ inner ℝ θ x) ∧
      P.directionalWidth θ = inner ℝ θ p - inner ℝ θ q := by
  simpa [directionalWidth] using
    IsCompact.exists_directionalWidth_eq P.isCompact P.nonempty θ

theorem inner_sub_inner_le_directionalWidth (P : IntrinsicBody E) (θ : E)
    {x y : E} (hx : x ∈ P) (hy : y ∈ P) :
    inner ℝ θ x - inner ℝ θ y ≤ P.directionalWidth θ := by
  exact ZeroOrderBounds.inner_sub_inner_le_directionalWidth
    P.isCompact P.nonempty θ hx hy

theorem inner_sub_le_directionalWidth (P : IntrinsicBody E) (θ : E)
    {x y : E} (hx : x ∈ P) (hy : y ∈ P) :
    inner ℝ θ (x - y) ≤ P.directionalWidth θ := by
  exact ZeroOrderBounds.inner_sub_le_directionalWidth P.isCompact P.nonempty θ hx hy

theorem directionalWidth_nonneg (P : IntrinsicBody E) (θ : E) :
    0 ≤ P.directionalWidth θ :=
  ZeroOrderBounds.directionalWidth_nonneg P.isCompact P.nonempty θ

theorem directionalWidth_smul_of_nonneg (P : IntrinsicBody E) (θ : E)
    {c : ℝ} (hc : 0 ≤ c) : P.directionalWidth (c • θ) = c * P.directionalWidth θ :=
  ZeroOrderBounds.directionalWidth_smul_of_nonneg P.isCompact P.nonempty θ hc

theorem directionalWidth_neg (P : IntrinsicBody E) (θ : E) :
    P.directionalWidth (-θ) = P.directionalWidth θ :=
  ZeroOrderBounds.directionalWidth_neg P.isCompact P.nonempty θ

theorem directionalWidth_smul (P : IntrinsicBody E) (θ : E) (c : ℝ) :
    P.directionalWidth (c • θ) = |c| * P.directionalWidth θ :=
  ZeroOrderBounds.directionalWidth_smul P.isCompact P.nonempty θ c

@[simp]
theorem directionalWidth_zero (P : IntrinsicBody E) : P.directionalWidth (0 : E) = 0 :=
  ZeroOrderBounds.directionalWidth_zero P.isCompact P.nonempty

theorem continuous_directionalWidth (P : IntrinsicBody E) :
    Continuous P.directionalWidth :=
  ZeroOrderBounds.continuous_directionalWidth P.isCompact

theorem measurable_directionalWidth (P : IntrinsicBody E) :
    Measurable P.directionalWidth :=
  ZeroOrderBounds.measurable_directionalWidth P.isCompact

theorem integrableOn_directionalWidth (P : IntrinsicBody E) {K : Set E}
    (hK : IsCompact K) (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    IntegrableOn P.directionalWidth K μ :=
  ZeroOrderBounds.integrableOn_directionalWidth P.isCompact hK μ

theorem directionalWidth_le_two_mul_norm (P : IntrinsicBody E) {r : ℝ}
    (hball : P.carrier ⊆ closedBall (0 : E) r) (θ : E) :
    P.directionalWidth θ ≤ 2 * r * ‖θ‖ :=
  ZeroOrderBounds.directionalWidth_le_two_mul_norm P.isCompact P.nonempty hball θ

theorem abs_directionalWidth_le_two_mul_norm (P : IntrinsicBody E) {r : ℝ}
    (hball : P.carrier ⊆ closedBall (0 : E) r) (θ : E) :
    |P.directionalWidth θ| ≤ 2 * r * ‖θ‖ :=
  ZeroOrderBounds.abs_directionalWidth_le_two_mul_norm P.isCompact P.nonempty hball θ

theorem sub_mem_directionSpan (P : IntrinsicBody E) {x y : E}
    (hx : x ∈ P) (hy : y ∈ P) : x - y ∈ P.directionSpan := by
  exact ZeroOrderBounds.sub_mem_directionSpan hx hy

/-- A body's width depends only on projection to the linear span of its chords. -/
theorem directionalWidth_starProjection_directionSpan (P : IntrinsicBody E) (θ : E) :
    P.directionalWidth (P.directionSpan.starProjection θ) = P.directionalWidth θ := by
  exact ZeroOrderBounds.directionalWidth_starProjection_directionSpan
    P.isCompact P.nonempty θ

theorem directionalWidth_eq_starProjection_directionSpan (P : IntrinsicBody E) (θ : E) :
    P.directionalWidth θ = P.directionalWidth (P.directionSpan.starProjection θ) :=
  (P.directionalWidth_starProjection_directionSpan θ).symm

theorem directionalWidth_eq_of_starProjection_eq (P : IntrinsicBody E) {θ φ : E}
    (hproj : P.directionSpan.starProjection θ = P.directionSpan.starProjection φ) :
    P.directionalWidth θ = P.directionalWidth φ := by
  exact ZeroOrderBounds.directionalWidth_eq_of_starProjection_eq
    P.isCompact P.nonempty hproj

theorem directionalWidth_eq_of_sub_mem_directionSpan_orthogonal
    (P : IntrinsicBody E) {θ φ : E} (horth : θ - φ ∈ P.directionSpanᗮ) :
    P.directionalWidth θ = P.directionalWidth φ := by
  exact ZeroOrderBounds.directionalWidth_eq_of_sub_mem_directionSpan_orthogonal
    P.isCompact P.nonempty horth

/-- Translation invariance, stated for the bundled translated body. -/
@[simp]
theorem directionalWidth_translate (P : IntrinsicBody E) (v θ : E) :
    (P.translate v).directionalWidth θ = P.directionalWidth θ := by
  exact ZeroOrderBounds.directionalWidth_translate_image P.isCompact P.nonempty v θ

end IntrinsicBody

end ZeroOrderBounds
