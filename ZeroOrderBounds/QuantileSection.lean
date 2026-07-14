import ZeroOrderBounds.IntrinsicVolume
import ZeroOrderBounds.AtomlessQuantile
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Integral.Average

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Exact quantiles and large affine sections

This file turns the one-dimensional atomless-quantile theorem into a geometric statement for
compact convex bodies.  It also records the codimension-one slicing estimate used by the resisting
oracle.
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Metric Set Topology

namespace ZeroOrderBounds

/-- Membership in an affine hyperplane orthogonal to a unit vector, in line coordinates. -/
theorem mem_orthogonalSlice_iff
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (p : P) {e : V} (he : ‖e‖ = 1)
    (x : ℝ) (q : P) :
    q ∈ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ ↔ inner ℝ e (q -ᵥ p) = x := by
  rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right,
    vsub_vadd_eq_vsub_sub, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he]
  norm_num
  exact sub_eq_zero

/-- A finite positive-measure set has a codimension-one orthogonal section at least as large as
its average over any interval containing all nonempty sections. -/
theorem exists_large_orthogonalSlice
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [MetricSpace P] [MeasurableSpace P] [BorelSpace P]
    [NormedAddTorsor V P] (p : P) {e : V} (he0 : e ≠ 0) (he : ‖e‖ = 1)
    {t : Set P} (htmeas : MeasurableSet t)
    (htfinite : μHE[Module.finrank ℝ V] t < ⊤)
    {a b : ℝ} (hab : a < b)
    (hsupport : ∀ x, (t ∩ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ).Nonempty →
      x ∈ Icc a b) :
    ∃ x ∈ Icc a b,
      μHE[Module.finrank ℝ V] t / ENNReal.ofReal (b - a) ≤
        μHE[Module.finrank ℝ V - 1]
          (t ∩ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ) := by
  let f : ℝ → ℝ≥0∞ := fun x ↦
    μHE[Module.finrank ℝ V - 1]
      (t ∩ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ)
  have hformula : μHE[Module.finrank ℝ V] t = ∫⁻ x, f x := by
    have h := EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral p he0 htmeas
    have he' : ‖e‖ₑ = 1 := by
      rw [← ofReal_norm, he]
      simp
    rw [he'] at h
    simpa [f] using h
  have hfsupport : Function.support f ⊆ Icc a b := by
    intro x hx
    apply hsupport x
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hx
    simp [f, hempty]
  have hIvol : volume (Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hint : (∫⁻ x in Icc a b, f x) ≠ ⊤ := by
    rw [setLIntegral_eq_of_support_subset hfsupport, ← hformula]
    exact htfinite.ne
  obtain ⟨x, hx, havg⟩ :=
    exists_setLAverage_le (f := f) hIvol measurableSet_Icc.nullMeasurableSet hint
  refine ⟨x, hx, ?_⟩
  rw [setLAverage_eq, setLIntegral_eq_of_support_subset hfsupport, ← hformula,
    Real.volume_Icc] at havg
  exact havg

/-- The Riesz vector of the linear part of a real-valued continuous affine map. -/
def affineRieszVector
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace P] [AddTorsor V P]
    [IsTopologicalAddTorsor P]
    (ℓ : P →ᴬ[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm ℓ.contLinear

theorem inner_affineRieszVector
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace P] [AddTorsor V P]
    [IsTopologicalAddTorsor P]
    (ℓ : P →ᴬ[ℝ] ℝ) (v : V) :
    inner ℝ (affineRieszVector ℓ) v = ℓ.contLinear v := by
  exact InnerProductSpace.toDual_symm_apply

theorem affineRieszVector_ne_zero
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace P] [AddTorsor V P]
    [IsTopologicalAddTorsor P]
    {ℓ : P →ᴬ[ℝ] ℝ} (hℓ : ℓ.contLinear ≠ 0) : affineRieszVector ℓ ≠ 0 := by
  intro hg
  apply hℓ
  apply ContinuousLinearMap.ext
  intro v
  rw [← inner_affineRieszVector ℓ v, hg]
  simp

/-- Orthogonal slices normal to the Riesz vector are precisely affine level sets. -/
theorem mem_rieszOrthogonalSlice_iff
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [IsTopologicalAddTorsor P]
    (ℓ : P →ᴬ[ℝ] ℝ) (hℓ : ℓ.contLinear ≠ 0) (p : P) (x : ℝ) (q : P) :
    let e := NormedSpace.normalize (affineRieszVector ℓ)
    q ∈ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ ↔ ℓ q = ℓ (x • e +ᵥ p) := by
  dsimp only
  let g := affineRieszVector ℓ
  let e := NormedSpace.normalize g
  change q ∈ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ ↔ ℓ q = ℓ (x • e +ᵥ p)
  have hg0 : g ≠ 0 := affineRieszVector_ne_zero hℓ
  have he : ‖e‖ = 1 := NormedSpace.norm_normalize hg0
  rw [mem_orthogonalSlice_iff p he]
  have hgscale : ‖g‖ • e = g := by
    simpa [e] using NormedSpace.norm_smul_normalize g
  have hlin (v : V) : ℓ.contLinear v = ‖g‖ * inner ℝ e v := by
    calc
      ℓ.contLinear v = inner ℝ g v := (inner_affineRieszVector ℓ v).symm
      _ = inner ℝ (‖g‖ • e) v := by rw [hgscale]
      _ = ‖g‖ * inner ℝ e v := real_inner_smul_left e v ‖g‖
  have hq : ℓ q - ℓ p = ‖g‖ * inner ℝ e (q -ᵥ p) := by
    calc
      ℓ q - ℓ p = ℓ.contLinear (q -ᵥ p) := (ℓ.contLinear_map_vsub q p).symm
      _ = _ := hlin _
  have hb : ℓ (x • e +ᵥ p) - ℓ p = ‖g‖ * x := by
    calc
      ℓ (x • e +ᵥ p) - ℓ p = ℓ.contLinear ((x • e +ᵥ p) -ᵥ p) :=
        (ℓ.contLinear_map_vsub (x • e +ᵥ p) p).symm
      _ = ‖g‖ * inner ℝ e ((x • e +ᵥ p) -ᵥ p) := hlin _
      _ = ‖g‖ * x := by
        rw [vadd_vsub, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
        ring
  constructor
  · intro hx
    rw [hx] at hq
    exact sub_left_inj.mp (hq.trans hb.symm)
  · intro hlevel
    have hprod : ‖g‖ * inner ℝ e (q -ᵥ p) = ‖g‖ * x := by
      calc
        ‖g‖ * inner ℝ e (q -ᵥ p) = ℓ q - ℓ p := hq.symm
        _ = ℓ (x • e +ᵥ p) - ℓ p := congrArg (fun z ↦ z - ℓ p) hlevel
        _ = ‖g‖ * x := hb
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hg0) hprod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A map is nonconstant on a set if it takes two different values there. -/
def NonconstantOn (f : E → ℝ) (P : Set E) : Prop :=
  ∃ x ∈ P, ∃ z ∈ P, f x ≠ f z

/-- The closed upper cap of `P` cut out by an affine functional. -/
def affineCap (P : Set E) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) : Set E :=
  P ∩ ℓ ⁻¹' Ici r

/-- The level section of `P` cut out by an affine functional. -/
def affineSection (P : Set E) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) : Set E :=
  P ∩ ℓ ⁻¹' {r}

theorem affineCap_subset (P : Set E) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) :
    affineCap P ℓ r ⊆ P :=
  inter_subset_left

theorem affineSection_subset (P : Set E) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) :
    affineSection P ℓ r ⊆ P :=
  inter_subset_left

theorem isCompact_affineCap {P : Set E} (hP : IsCompact P) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) :
    IsCompact (affineCap P ℓ r) := by
  exact hP.inter_right (isClosed_Ici.preimage ℓ.continuous)

theorem isCompact_affineSection {P : Set E} (hP : IsCompact P) (ℓ : E →ᴬ[ℝ] ℝ)
    (r : ℝ) : IsCompact (affineSection P ℓ r) := by
  exact hP.inter_right (isClosed_singleton.preimage ℓ.continuous)

theorem convex_affineCap {P : Set E} (hP : Convex ℝ P) (ℓ : E →ᴬ[ℝ] ℝ) (r : ℝ) :
    Convex ℝ (affineCap P ℓ r) := by
  exact hP.inter ((convex_Ici r).affine_preimage ℓ.toAffineMap)

theorem convex_affineSection {P : Set E} (hP : Convex ℝ P) (ℓ : E →ᴬ[ℝ] ℝ)
    (r : ℝ) : Convex ℝ (affineSection P ℓ r) := by
  exact hP.inter ((convex_singleton r).affine_preimage ℓ.toAffineMap)

/-- A nonconstant affine functional has fibers of strictly smaller affine dimension inside `P`.
This formulation, which does not assume convexity, is convenient for proving atomlessness. -/
theorem affineDim_affineSection_lt {P : Set E} {ℓ : E →ᴬ[ℝ] ℝ}
    (hnonconst : NonconstantOn ℓ P) (r : ℝ)
    (hne : (affineSection P ℓ r).Nonempty) :
    affineDim (affineSection P ℓ r) < affineDim P := by
  let Q := affineSection P ℓ r
  let A := affineSpan ℝ P
  let B := affineSpan ℝ Q
  have hQP : Q ⊆ P := affineSection_subset P ℓ r
  have hBA : B ≤ A := affineSpan_mono ℝ hQP
  have hdirle : B.direction ≤ A.direction := AffineSubspace.direction_le hBA
  have hdimle : Module.finrank ℝ B.direction ≤ Module.finrank ℝ A.direction :=
    Submodule.finrank_mono hdirle
  refine lt_of_le_of_ne hdimle ?_
  intro hdimeq
  have hdir : B.direction = A.direction :=
    Submodule.eq_of_le_of_finrank_eq hdirle hdimeq
  obtain ⟨p, hpQ⟩ := hne
  let H : AffineSubspace ℝ E := AffineSubspace.mk' p ℓ.contLinear.ker
  have hQH : Q ⊆ H := by
    intro q hq
    change q ∈ AffineSubspace.mk' p ℓ.contLinear.ker
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    have hqlevel : ℓ q = r := hq.2
    have hplevel : ℓ p = r := hpQ.2
    calc
      ℓ.contLinear (q - p) = ℓ q - ℓ p := ℓ.contLinear_map_vsub q p
      _ = 0 := sub_eq_zero.mpr (hqlevel.trans hplevel.symm)
  have hBH : B ≤ H := affineSpan_le.mpr hQH
  have hBker : B.direction ≤ ℓ.contLinear.ker := by
    simpa [H] using AffineSubspace.direction_le hBH
  obtain ⟨x, hxP, z, hzP, hxz⟩ := hnonconst
  have hxzA : x - z ∈ A.direction :=
    A.vsub_mem_direction (subset_affineSpan ℝ P hxP) (subset_affineSpan ℝ P hzP)
  have hxzker : x - z ∈ ℓ.contLinear.ker := by
    apply hBker
    rw [hdir]
    exact hxzA
  rw [LinearMap.mem_ker] at hxzker
  have hxzeq : ℓ x - ℓ z = 0 := by
    calc
      ℓ x - ℓ z = ℓ.contLinear (x - z) := (ℓ.contLinear_map_vsub x z).symm
      _ = 0 := hxzker
  exact hxz (sub_eq_zero.mp hxzeq)

/-- Every level fiber of a nonconstant affine functional is null for full intrinsic-dimensional
Euclidean Hausdorff measure. -/
theorem euclideanHausdorffMeasure_affineSection_eq_zero {P : Set E}
    (hPcompact : IsCompact P) {ℓ : E →ᴬ[ℝ] ℝ} (hnonconst : NonconstantOn ℓ P)
    (r : ℝ) : μHE[affineDim P] (affineSection P ℓ r) = 0 := by
  by_cases hne : (affineSection P ℓ r).Nonempty
  · have hlt := affineDim_affineSection_lt hnonconst r hne
    rcases Measure.euclideanHausdorffMeasure_zero_or_top hlt (affineSection P ℓ r) with
      hzero | htop
    · exact hzero
    · have hfinite : μHE[affineDim (affineSection P ℓ r)]
          (affineSection P ℓ r) < ⊤ :=
        euclideanHausdorffMeasure_affineDim_lt_top hne
          (isCompact_affineSection hPcompact ℓ r)
      exact (hfinite.ne htop).elim
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact measure_empty

/-- A positive codimension-one measure forces a level section to have exactly codimension one. -/
theorem affineDim_affineSection_eq_sub_one_of_pos {P : Set E}
    (hPcompact : IsCompact P) {ℓ : E →ᴬ[ℝ] ℝ} (hnonconst : NonconstantOn ℓ P)
    (r : ℝ) (hpos : 0 < μHE[affineDim P - 1] (affineSection P ℓ r)) :
    affineDim (affineSection P ℓ r) = affineDim P - 1 := by
  have hne : (affineSection P ℓ r).Nonempty :=
    nonempty_of_euclideanHausdorffMeasure_pos hpos
  have hlt : affineDim (affineSection P ℓ r) < affineDim P :=
    affineDim_affineSection_lt hnonconst r hne
  have hle : affineDim (affineSection P ℓ r) ≤ affineDim P - 1 :=
    Nat.le_sub_one_of_lt hlt
  apply le_antisymm hle
  apply Nat.le_of_not_gt
  intro hsmall
  rcases Measure.euclideanHausdorffMeasure_zero_or_top hsmall (affineSection P ℓ r) with
    hzero | htop
  · exact hpos.ne' hzero
  · have hfinite : μHE[affineDim (affineSection P ℓ r)]
        (affineSection P ℓ r) < ⊤ :=
      euclideanHausdorffMeasure_affineDim_lt_top hne
        (isCompact_affineSection hPcompact ℓ r)
    exact hfinite.ne htop

/-- Exact upper quantiles for intrinsic volume on a compact positive-dimensional body. -/
theorem exists_affineCap_euclideanHausdorffMeasure_eq {P : Set E}
    (hPne : P.Nonempty) (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {ℓ : E →ᴬ[ℝ] ℝ}
    (hnonconst : NonconstantOn ℓ P) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ r, μHE[affineDim P] (affineCap P ℓ r) =
      ENNReal.ofReal α * μHE[affineDim P] P := by
  let μ : Measure E := μHE[affineDim P].restrict P
  haveI : IsFiniteMeasure μ :=
    ⟨by
      rw [show μ Set.univ = μHE[affineDim P] P by
        simp [μ]]
      exact euclideanHausdorffMeasure_affineDim_lt_top hPne hPcompact⟩
  have hμ0 : μ Set.univ ≠ 0 := by
    rw [show μ Set.univ = μHE[affineDim P] P by
      simp [μ]]
    exact (euclideanHausdorffMeasure_affineDim_pos_of_nonempty_convex hPne hPconvex).ne'
  have hfiber : ∀ y, μ (ℓ ⁻¹' {y}) = 0 := by
    intro y
    rw [Measure.restrict_apply
      ((measurableSet_singleton y).preimage ℓ.continuous.measurable)]
    rw [inter_comm]
    exact euclideanHausdorffMeasure_affineSection_eq_zero hPcompact hnonconst y
  obtain ⟨r, hr⟩ := exists_map_Ici_measure_eq μ ℓ ℓ.continuous.measurable hμ0 hfiber hα0 hα1
  refine ⟨r, ?_⟩
  rw [show μ (ℓ ⁻¹' Ici r) = μHE[affineDim P] (affineCap P ℓ r) by
      rw [Measure.restrict_apply (measurableSet_Ici.preimage ℓ.continuous.measurable)]
      exact congrArg _ (inter_comm _ _),
    show μ Set.univ = μHE[affineDim P] P by simp [μ]] at hr
  exact hr

/-- A positive upper cap of a body in the radius-`τ` ball has a large codimension-one level
section.  The denominator is the length `2 * τ` of the line-coordinate support. -/
theorem exists_large_affineSection {P : Set E}
    (hPne : P.Nonempty) (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {ℓ : E →ᴬ[ℝ] ℝ} (hnonconst : NonconstantOn ℓ P)
    {τ r : ℝ} (hτ : 0 < τ) (hball : P ⊆ closedBall (0 : E) τ)
    (hcap_pos : 0 < μHE[affineDim P] (affineCap P ℓ r)) :
    ∃ y, r ≤ y ∧
      μHE[affineDim P] (affineCap P ℓ r) / ENNReal.ofReal (2 * τ) ≤
        μHE[affineDim P - 1] (affineSection P ℓ y) ∧
      (affineSection P ℓ y).Nonempty ∧
      IsCompact (affineSection P ℓ y) ∧
      Convex ℝ (affineSection P ℓ y) ∧
      affineDim (affineSection P ℓ y) = affineDim P - 1 := by
  let A := affineSpan ℝ P
  let p : A := ⟨hPne.some, subset_affineSpan ℝ P hPne.some_mem⟩
  letI : Nonempty A := ⟨p⟩
  let ℓA : A →ᴬ[ℝ] ℝ := ℓ.comp A.subtypeA
  have hℓA : ℓA.contLinear ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := (ContinuousAffineMap.contLinear_eq_zero_iff_exists_const ℓA).mp hzero
    obtain ⟨x, hxP, z, hzP, hxz⟩ := hnonconst
    let xA : A := ⟨x, subset_affineSpan ℝ P hxP⟩
    let zA : A := ⟨z, subset_affineSpan ℝ P hzP⟩
    apply hxz
    change ℓA xA = ℓA zA
    rw [hc]
    rfl
  let g : A.direction := affineRieszVector ℓA
  let e : A.direction := NormedSpace.normalize g
  have hg0 : g ≠ 0 := affineRieszVector_ne_zero hℓA
  have he0 : e ≠ 0 := by
    intro hezero
    exact hg0 ((NormedSpace.normalize_eq_zero_iff g).mp hezero)
  have he : ‖e‖ = 1 := NormedSpace.norm_normalize hg0
  let C : Set E := affineCap P ℓ r
  let t : Set A := Subtype.val ⁻¹' C
  have ht_image : Subtype.val '' t = C := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x, subset_affineSpan ℝ P (affineCap_subset P ℓ r hx)⟩, hx, rfl⟩
  have hCcompact : IsCompact C := isCompact_affineCap hPcompact ℓ r
  have htmeas : MeasurableSet t :=
    hCcompact.isClosed.measurableSet.preimage measurable_subtype_coe
  have hCfinite : μHE[affineDim P] C < ⊤ := by
    exact (measure_mono (affineCap_subset P ℓ r)).trans_lt
      (euclideanHausdorffMeasure_affineDim_lt_top hPne hPcompact)
  have htmeasure : μHE[Module.finrank ℝ A.direction] t = μHE[affineDim P] C := by
    rw [← A.euclideanHausdorffMeasure_coe_image (Module.finrank ℝ A.direction) t,
      ht_image]
    rfl
  have htfinite : μHE[Module.finrank ℝ A.direction] t < ⊤ := by
    rw [htmeasure]
    exact hCfinite
  let c : ℝ := -inner ℝ (e : E) p.val
  have hsupport (x : ℝ)
      (hx : (t ∩ AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ).Nonempty) :
      x ∈ Icc (c - τ) (c + τ) := by
    obtain ⟨q, hqt, hqplane⟩ := hx
    have hqC : q.val ∈ C := hqt
    have hqP : q.val ∈ P := affineCap_subset P ℓ r hqC
    have hxcoord : inner ℝ e (q -ᵥ p) = x :=
      (mem_orthogonalSlice_iff (V := A.direction) (P := A) p he x q).mp hqplane
    have hxcoordE : inner ℝ (e : E) (q.val - p.val) = x := by
      calc
        inner ℝ (e : E) (q.val - p.val) = inner ℝ (e : E) ((q -ᵥ p : A.direction) : E) := by
          exact congrArg (fun v : E ↦ inner ℝ (e : E) v)
            (by simpa only [vsub_eq_sub] using (A.coe_vsub q p).symm)
        _ = inner ℝ e (q -ᵥ p) := (A.direction.coe_inner e (q -ᵥ p)).symm
        _ = x := hxcoord
    have hshift : x + inner ℝ (e : E) p.val = inner ℝ (e : E) q.val := by
      rw [← hxcoordE, inner_sub_right]
      ring
    have hqnorm : ‖q.val‖ ≤ τ := by
      simpa [mem_closedBall, dist_eq_norm] using hball hqP
    have habs : |inner ℝ (e : E) q.val| ≤ τ := by
      calc
        |inner ℝ (e : E) q.val| ≤ ‖(e : E)‖ * ‖q.val‖ :=
          abs_real_inner_le_norm (e : E) q.val
        _ = ‖q.val‖ := by
          rw [show ‖(e : E)‖ = 1 from (Submodule.norm_coe e).trans he]
          simp
        _ ≤ τ := hqnorm
    have habs' := abs_le.mp habs
    dsimp [c]
    constructor <;> linarith
  have hab : c - τ < c + τ := by linarith
  obtain ⟨x, hxI, hxlarge⟩ :=
    exists_large_orthogonalSlice (V := A.direction) (P := A) p he0 he
      (t := t) htmeas htfinite (a := c - τ) (b := c + τ) hab hsupport
  let H : AffineSubspace ℝ A := AffineSubspace.mk' (x • e +ᵥ p) (ℝ ∙ e)ᗮ
  let sA : Set A := t ∩ H
  let y : ℝ := ℓA (x • e +ᵥ p)
  have hlen : (c + τ) - (c - τ) = 2 * τ := by ring
  have hsApos : 0 < μHE[Module.finrank ℝ A.direction - 1] sA := by
    have hquotpos : 0 < μHE[Module.finrank ℝ A.direction] t /
        ENNReal.ofReal ((c + τ) - (c - τ)) :=
      ENNReal.div_pos (by rw [htmeasure]; exact hcap_pos.ne') ENNReal.ofReal_ne_top
    exact hquotpos.trans_le (by simpa [sA, H] using hxlarge)
  have hsAne : sA.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hsAempty
    apply (ne_of_gt hsApos)
    rw [hsAempty]
    exact measure_empty
  have hry : r ≤ y := by
    obtain ⟨q, hqsA⟩ := hsAne
    have hqsA' : q ∈ t ∩ (H : Set A) := by simpa [sA] using hqsA
    have hqt : q ∈ t := hqsA'.1
    have hqH : q ∈ H := hqsA'.2
    have hqC : q.val ∈ C := hqt
    have hqcap : r ≤ ℓ q.val := hqC.2
    have hqlevel : ℓA q = y := by
      exact (mem_rieszOrthogonalSlice_iff (V := A.direction) (P := A)
        ℓA hℓA p x q).mp hqH
    have hqlevelE : ℓ q.val = y := by
      simpa [ℓA, y, ContinuousAffineMap.coe_comp] using hqlevel
    exact hqcap.trans_eq hqlevelE
  have hsA_image : Subtype.val '' sA = affineSection P ℓ y := by
    ext q
    constructor
    · rintro ⟨qA, hqsA, rfl⟩
      have hqsA' : qA ∈ t ∩ (H : Set A) := by simpa [sA] using hqsA
      have hqt : qA ∈ t := hqsA'.1
      have hqH : qA ∈ H := hqsA'.2
      have hqC : qA.val ∈ C := hqt
      have hlevel := (mem_rieszOrthogonalSlice_iff (V := A.direction) (P := A)
        ℓA hℓA p x qA).mp hqH
      have hlevel' : ℓ qA.val = y := by
        simpa [ℓA, y, ContinuousAffineMap.coe_comp] using hlevel
      exact ⟨affineCap_subset P ℓ r hqC, hlevel'⟩
    · intro hq
      let qA : A := ⟨q, subset_affineSpan ℝ P hq.1⟩
      have hqC : qA ∈ t := by
        change q ∈ C
        exact ⟨hq.1, hry.trans_eq hq.2.symm⟩
      have hqH : qA ∈ H := by
        apply (mem_rieszOrthogonalSlice_iff (V := A.direction) (P := A)
          ℓA hℓA p x qA).mpr
        simpa [ℓA, y, ContinuousAffineMap.coe_comp] using hq.2
      have hqsA : qA ∈ sA := by
        change qA ∈ t ∩ (H : Set A)
        exact ⟨hqC, hqH⟩
      exact ⟨qA, hqsA, rfl⟩
  have hsmeasure : μHE[Module.finrank ℝ A.direction - 1] sA =
      μHE[affineDim P - 1] (affineSection P ℓ y) := by
    rw [← A.euclideanHausdorffMeasure_coe_image (Module.finrank ℝ A.direction - 1) sA,
      hsA_image]
    rfl
  have hlarge : μHE[affineDim P] C / ENNReal.ofReal (2 * τ) ≤
      μHE[affineDim P - 1] (affineSection P ℓ y) := by
    rw [← htmeasure, ← hsmeasure, ← hlen]
    simpa [sA, H] using hxlarge
  have hspos : 0 < μHE[affineDim P - 1] (affineSection P ℓ y) := by
    rw [← hsmeasure]
    exact hsApos
  have hsne : (affineSection P ℓ y).Nonempty := by
    rw [← hsA_image]
    exact hsAne.image Subtype.val
  have hscompact : IsCompact (affineSection P ℓ y) :=
    isCompact_affineSection hPcompact ℓ y
  have hsconvex : Convex ℝ (affineSection P ℓ y) :=
    convex_affineSection hPconvex ℓ y
  have hsdim : affineDim (affineSection P ℓ y) = affineDim P - 1 :=
    affineDim_affineSection_eq_sub_one_of_pos hPcompact hnonconst y hspos
  exact ⟨y, hry, hlarge, hsne, hscompact, hsconvex, hsdim⟩

end ZeroOrderBounds
