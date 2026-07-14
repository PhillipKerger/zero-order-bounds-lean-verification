import ZeroOrderBounds.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Intrinsic Euclidean volume

This file supplies the relative-volume bookkeeping used by the resisting oracle.  A set is
measured with Euclidean Hausdorff measure in the dimension of its affine hull.  Dimension zero is
given the explicit volume convention `1`; this is exactly the value for a nonempty singleton and
keeps later products free of exceptional cases.

The main technical device below is to pull a set contained in an affine subspace back to the
direction space by the isometry `IsometryEquiv.vaddConst`.  There the full-dimensional Euclidean
Hausdorff measure is ordinary Haar volume, so compact sets have finite measure.
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Metric Set

namespace ZeroOrderBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The affine dimension of a subset of a finite-dimensional real vector space. -/
def affineDim (s : Set E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ s).direction

/-- Intrinsic Euclidean Hausdorff volume.  Nonempty zero-dimensional bodies have volume one. -/
def intrinsicVolume (s : Set E) : ℝ≥0∞ :=
  if affineDim s = 0 then 1 else μHE[affineDim s] s

/-- The real-valued intrinsic volume, used only after finiteness has been established. -/
def intrinsicVolumeReal (s : Set E) : ℝ :=
  (intrinsicVolume s).toReal

/-- Volume of the unit ball in Euclidean dimension `k`, with the dimension-zero convention. -/
def kappa (k : ℕ) : ℝ≥0∞ :=
  if k = 0 then 1
  else volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)

@[simp]
theorem intrinsicVolume_of_affineDim_eq_zero {s : Set E} (h : affineDim s = 0) :
    intrinsicVolume s = 1 := by
  simp [intrinsicVolume, h]

theorem intrinsicVolume_of_affineDim_ne_zero {s : Set E} (h : affineDim s ≠ 0) :
    intrinsicVolume s = μHE[affineDim s] s := by
  simp [intrinsicVolume, h]

@[simp]
theorem kappa_zero : kappa 0 = 1 := by
  simp [kappa]

theorem kappa_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    kappa k = volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  simp [kappa, hk]

/-- Real-valued unit-ball volume. -/
def kappaReal (k : ℕ) : ℝ :=
  (kappa k).toReal

theorem kappa_pos (k : ℕ) : 0 < kappa k := by
  by_cases hk : k = 0
  · simp [hk]
  · letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
    rw [kappa_of_ne_zero hk]
    exact Metric.measure_closedBall_pos volume 0 zero_lt_one

theorem kappa_lt_top (k : ℕ) : kappa k < ⊤ := by
  by_cases hk : k = 0
  · simp [hk]
  · letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
    rw [kappa_of_ne_zero hk]
    exact measure_closedBall_lt_top

theorem kappaReal_pos (k : ℕ) : 0 < kappaReal k :=
  ENNReal.toReal_pos (kappa_pos k).ne' (kappa_lt_top k).ne

@[simp]
theorem kappaReal_zero : kappaReal 0 = 1 := by
  simp [kappaReal]

theorem ofReal_kappaReal (k : ℕ) : ENNReal.ofReal (kappaReal k) = kappa k :=
  ENNReal.ofReal_toReal (kappa_lt_top k).ne

/-- The volume of a ball in any positive-dimensional Euclidean space depends only on its
dimension and radius. -/
theorem volume_closedBall_eq_rpow_mul_kappa
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {k : ℕ} (hk : Module.finrank ℝ V = k) (hk0 : k ≠ 0) (r : ℝ) :
    volume (closedBall (0 : V) r) = ENNReal.ofReal r ^ k * kappa k := by
  letI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (hk ▸ Nat.pos_of_ne_zero hk0)
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk0)
  rw [InnerProductSpace.volume_closedBall, hk, kappa_of_ne_zero hk0,
    EuclideanSpace.volume_closedBall]
  simp

/-- The closed ball of radius `r` inside an affine subspace, viewed in the ambient space. -/
def affineClosedBall (A : AffineSubspace ℝ E) (p : A) (r : ℝ) : Set E :=
  Subtype.val '' closedBall p r

@[simp]
theorem mem_affineClosedBall_iff (A : AffineSubspace ℝ E) (p : A) (r : ℝ) (x : E) :
    x ∈ affineClosedBall A p r ↔ x ∈ A ∧ dist x p ≤ r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    have hydist := mem_closedBall.mp hy
    rw [Subtype.dist_eq] at hydist
    simpa [dist_comm] using hydist
  · rintro ⟨hxA, hdist⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    apply mem_closedBall.mpr
    rw [Subtype.dist_eq]
    simpa [dist_comm] using hdist

/-- The intrinsic measure of a positive-dimensional relative ball. -/
theorem euclideanHausdorffMeasure_affineClosedBall
    (A : AffineSubspace ℝ E) (p : A)
    (hposdim : Module.finrank ℝ A.direction ≠ 0) (r : ℝ) :
    μHE[Module.finrank ℝ A.direction] (affineClosedBall A p r) =
      ENNReal.ofReal r ^ Module.finrank ℝ A.direction *
        kappa (Module.finrank ℝ A.direction) := by
  letI : Nonempty A := ⟨p⟩
  rw [affineClosedBall, A.euclideanHausdorffMeasure_coe_image]
  let e : A.direction ≃ᵢ A := IsometryEquiv.vaddConst p
  calc
    μHE[Module.finrank ℝ A.direction] (closedBall p r) =
        volume (e ⁻¹' closedBall p r) := by
      symm
      exact (EuclideanGeometry.measurePreserving_vaddConst p).measure_preimage_equiv
        (f := e.toHomeomorph.toMeasurableEquiv) (closedBall p r)
    _ = volume (closedBall (0 : A.direction) r) := by
      rw [e.preimage_closedBall]
      simp [e]
    _ = ENNReal.ofReal r ^ Module.finrank ℝ A.direction *
          kappa (Module.finrank ℝ A.direction) :=
      volume_closedBall_eq_rpow_mul_kappa rfl hposdim r

/-- A set lying in a positive-dimensional relative ball has at most the ball's intrinsic
Hausdorff measure. -/
theorem euclideanHausdorffMeasure_le_ball_of_subset
    (A : AffineSubspace ℝ E) (p : A)
    (hposdim : Module.finrank ℝ A.direction ≠ 0) {s : Set E} {r : ℝ}
    (hsub : s ⊆ affineClosedBall A p r) :
    μHE[Module.finrank ℝ A.direction] s ≤
      ENNReal.ofReal r ^ Module.finrank ℝ A.direction *
        kappa (Module.finrank ℝ A.direction) := by
  calc
    μHE[Module.finrank ℝ A.direction] s ≤
        μHE[Module.finrank ℝ A.direction] (affineClosedBall A p r) :=
      measure_mono hsub
    _ = _ := euclideanHausdorffMeasure_affineClosedBall A p hposdim r

/-- Intrinsic-volume upper bound from a ball centered at a point of the affine hull. -/
theorem intrinsicVolume_le_ball_of_center_mem_affineSpan
    {s : Set E} {p : E} {r : ℝ} (hp : p ∈ affineSpan ℝ s)
    (hball : ∀ x ∈ s, dist x p ≤ r) :
    intrinsicVolume s ≤
      ENNReal.ofReal r ^ affineDim s * kappa (affineDim s) := by
  by_cases hdim : affineDim s = 0
  · simp [intrinsicVolume, kappa, hdim]
  · rw [intrinsicVolume_of_affineDim_ne_zero hdim]
    let A := affineSpan ℝ s
    let pA : A := ⟨p, hp⟩
    apply euclideanHausdorffMeasure_le_ball_of_subset A pA
      (by simpa [affineDim, A] using hdim)
    intro x hx
    rw [mem_affineClosedBall_iff]
    exact ⟨subset_affineSpan ℝ s hx, hball x hx⟩

/-- Elementary bounded-diameter estimate: choosing any point of the body as center costs no
isodiametric theorem. -/
theorem intrinsicVolume_le_of_forall_dist_le {s : Set E} {p : E} {r : ℝ}
    (hp : p ∈ s) (hdiam : ∀ x ∈ s, dist x p ≤ r) :
    intrinsicVolume s ≤
      ENNReal.ofReal r ^ affineDim s * kappa (affineDim s) :=
  intrinsicVolume_le_ball_of_center_mem_affineSpan
    (subset_affineSpan ℝ s hp) hdiam

/-- Strict pairwise diameter bounds imply the same weak intrinsic-volume estimate. -/
theorem intrinsicVolume_le_of_pairwise_dist_lt {s : Set E} {r : ℝ}
    (hne : s.Nonempty) (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y < r) :
    intrinsicVolume s ≤
      ENNReal.ofReal r ^ affineDim s * kappa (affineDim s) := by
  exact intrinsicVolume_le_of_forall_dist_le hne.some_mem fun x hx ↦
    (hdiam x hx hne.some hne.some_mem).le

/-- The closest point of an affine hull to the origin can be used as a relative-ball center.  This
is the elementary projection argument behind the sharp ambient-ball bound. -/
theorem exists_affineSpan_center_dist_le_of_subset_closedBall
    {s : Set E} {r : ℝ} (hne : s.Nonempty) (hball : s ⊆ closedBall (0 : E) r) :
    ∃ c ∈ affineSpan ℝ s, ∀ x ∈ s, dist x c ≤ r := by
  let A := affineSpan ℝ s
  let D := A.direction
  let p : E := hne.some
  have hp : p ∈ A := subset_affineSpan ℝ s hne.some_mem
  let c : E := p - D.starProjection p
  have hproj : D.starProjection p ∈ D := by
    rw [Submodule.starProjection_apply]
    exact (D.orthogonalProjectionOnto p).property
  have hc : c ∈ A := by
    apply (A.vsub_right_mem_direction_iff_mem hp c).mp
    change c - p ∈ D
    have hcp : c - p = -D.starProjection p := by
      simp [c]
    rw [hcp]
    exact D.neg_mem hproj
  have hcorth : c ∈ Dᗮ := by
    simpa [c] using D.sub_starProjection_mem_orthogonal p
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hxA : x ∈ A := subset_affineSpan ℝ s hx
  have hxc : x - c ∈ D := A.vsub_mem_direction hxA hc
  have hinner : inner ℝ c (x - c) = 0 :=
    D.inner_left_of_mem_orthogonal hxc hcorth
  have hpyth : ‖x‖ * ‖x‖ = ‖c‖ * ‖c‖ + ‖x - c‖ * ‖x - c‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero c (x - c) hinner
    have hsum : c + (x - c) = x := by abel
    simpa only [hsum] using h
  have hsq : ‖x - c‖ * ‖x - c‖ ≤ ‖x‖ * ‖x‖ := by
    rw [hpyth]
    exact le_add_of_nonneg_left (mul_self_nonneg ‖c‖)
  have hnorm : ‖x - c‖ ≤ ‖x‖ :=
    nonneg_le_nonneg_of_sq_le_sq (norm_nonneg x) hsq
  have hxnorm : ‖x‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hball hx
  simpa [dist_eq_norm] using hnorm.trans hxnorm

/-- Maximum intrinsic volume inside an ambient Euclidean ball. -/
theorem intrinsicVolume_le_of_subset_closedBall {s : Set E} {r : ℝ}
    (hne : s.Nonempty) (hball : s ⊆ closedBall (0 : E) r) :
    intrinsicVolume s ≤
      ENNReal.ofReal r ^ affineDim s * kappa (affineDim s) := by
  obtain ⟨c, hc, hdist⟩ :=
    exists_affineSpan_center_dist_le_of_subset_closedBall hne hball
  exact intrinsicVolume_le_ball_of_center_mem_affineSpan hc hdist

/-- A compact set contained in a finite-dimensional affine subspace has finite Hausdorff measure
in the dimension of that affine subspace. -/
theorem euclideanHausdorffMeasure_lt_top_of_isCompact_of_subset_affineSubspace
    (A : AffineSubspace ℝ E) [Nonempty A] {s : Set E} (hs : IsCompact s)
    (hsub : s ⊆ A) :
    μHE[Module.finrank ℝ A.direction] s < ⊤ := by
  let t : Set A := Subtype.val ⁻¹' s
  have ht_image : Subtype.val '' t = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  rw [← ht_image, A.euclideanHausdorffMeasure_coe_image]
  let p : A := Classical.choice (inferInstance : Nonempty A)
  let e : A.direction ≃ᵢ A := IsometryEquiv.vaddConst p
  have ht : IsCompact t := by
    rw [Subtype.isCompact_iff, ht_image]
    exact hs
  have hpre : IsCompact (e ⁻¹' t) :=
    e.toHomeomorph.isCompact_preimage.mpr ht
  rw [← (EuclideanGeometry.measurePreserving_vaddConst p).measure_preimage_equiv
    (f := (IsometryEquiv.vaddConst p).toHomeomorph.toMeasurableEquiv) t]
  simpa [e] using hpre.measure_lt_top

/-- Raw Hausdorff measure in the affine dimension is finite for a nonempty compact set. -/
theorem euclideanHausdorffMeasure_affineDim_lt_top {s : Set E}
    (hne : s.Nonempty) (hcompact : IsCompact s) :
    μHE[affineDim s] s < ⊤ := by
  let A := affineSpan ℝ s
  letI : Nonempty A :=
    ⟨⟨hne.some, subset_affineSpan ℝ s hne.some_mem⟩⟩
  simpa [affineDim, A] using
    euclideanHausdorffMeasure_lt_top_of_isCompact_of_subset_affineSubspace
      A hcompact (subset_affineSpan ℝ s)

/-- Intrinsic volume of a nonempty compact set is finite. -/
theorem intrinsicVolume_lt_top {s : Set E} (hne : s.Nonempty) (hcompact : IsCompact s) :
    intrinsicVolume s < ⊤ := by
  by_cases hdim : affineDim s = 0
  · simp [intrinsicVolume, hdim]
  · rw [intrinsicVolume_of_affineDim_ne_zero hdim]
    exact euclideanHausdorffMeasure_affineDim_lt_top hne hcompact

/-- A nonempty convex set has positive Hausdorff measure in the dimension of its affine hull. -/
theorem euclideanHausdorffMeasure_affineDim_pos_of_nonempty_convex
    {s : Set E} (hne : s.Nonempty) (hconvex : Convex ℝ s) :
    0 < μHE[affineDim s] s := by
  let A := affineSpan ℝ s
  letI : Nonempty A :=
    ⟨⟨hne.some, subset_affineSpan ℝ s hne.some_mem⟩⟩
  let t : Set A := Subtype.val ⁻¹' s
  have ht_image : Subtype.val '' t = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_affineSpan ℝ s hx⟩, hx, rfl⟩
  have ht_interior : (interior t).Nonempty := by
    simpa [intrinsicInterior, t] using hne.intrinsicInterior hconvex
  let p : A := Classical.choice (inferInstance : Nonempty A)
  let e : A.direction ≃ᵢ A := IsometryEquiv.vaddConst p
  have hpre_interior : (interior (e ⁻¹' t)).Nonempty := by
    obtain ⟨y, hy⟩ := ht_interior
    refine ⟨e.symm y, ?_⟩
    have heq : interior (e ⁻¹' t) = e ⁻¹' interior t := by
      simpa using (e.toHomeomorph.preimage_interior t).symm
    rw [heq]
    simpa using hy
  have hvol : 0 < volume (e ⁻¹' t) :=
    Measure.measure_pos_of_nonempty_interior volume hpre_interior
  change 0 < μHE[Module.finrank ℝ A.direction] s
  rw [← ht_image, A.euclideanHausdorffMeasure_coe_image]
  rw [← (EuclideanGeometry.measurePreserving_vaddConst p).measure_preimage_equiv
    (f := e.toHomeomorph.toMeasurableEquiv) t]
  simpa using hvol

/-- Intrinsic volume is positive for every nonempty convex set. -/
theorem intrinsicVolume_pos_of_nonempty_convex {s : Set E}
    (hne : s.Nonempty) (hconvex : Convex ℝ s) : 0 < intrinsicVolume s := by
  by_cases hdim : affineDim s = 0
  · simp [intrinsicVolume, hdim]
  · rw [intrinsicVolume_of_affineDim_ne_zero hdim]
    exact euclideanHausdorffMeasure_affineDim_pos_of_nonempty_convex hne hconvex

/-- Affine dimension is bounded by the dimension of the ambient space. -/
theorem affineDim_le_finrank (s : Set E) : affineDim s ≤ Module.finrank ℝ E := by
  unfold affineDim
  simpa only [finrank_top] using
    (Submodule.finrank_mono (show (affineSpan ℝ s).direction ≤ ⊤ from le_top))

/-- A nonempty zero-dimensional set consists of a single point. -/
theorem eq_singleton_of_nonempty_of_affineDim_eq_zero {s : Set E}
    (hne : s.Nonempty) (hdim : affineDim s = 0) : s = {hne.some} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hdirzero : (affineSpan ℝ s).direction = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa [affineDim] using hdim
    have hv : x - hne.some ∈ (affineSpan ℝ s).direction :=
      (affineSpan ℝ s).vsub_mem_direction
        (subset_affineSpan ℝ s hx) (subset_affineSpan ℝ s hne.some_mem)
    rw [hdirzero] at hv
    have hzero : x - hne.some = 0 := by simpa using hv
    simpa using sub_eq_zero.mp hzero
  · exact Set.singleton_subset_iff.mpr hne.some_mem

/-- The explicit zero-dimensional convention agrees with Euclidean Hausdorff measure. -/
theorem euclideanHausdorffMeasure_zero_of_nonempty_affineDim_zero {s : Set E}
    (hne : s.Nonempty) (hdim : affineDim s = 0) : μHE[0] s = 1 := by
  rw [eq_singleton_of_nonempty_of_affineDim_eq_zero hne hdim,
    Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]

/-- Intrinsic volume is monotone between sets with the same affine dimension. -/
theorem intrinsicVolume_mono_of_subset_of_affineDim_eq {s t : Set E}
    (hst : s ⊆ t) (hdim : affineDim s = affineDim t) :
    intrinsicVolume s ≤ intrinsicVolume t := by
  by_cases hzero : affineDim t = 0
  · simp [intrinsicVolume, hzero, hdim]
  · rw [intrinsicVolume_of_affineDim_ne_zero (hdim.trans_ne hzero),
      intrinsicVolume_of_affineDim_ne_zero hzero, hdim]
    exact measure_mono hst

/-- Real intrinsic volume is positive once positivity and compactness are available. -/
theorem intrinsicVolumeReal_pos {s : Set E} (hne : s.Nonempty) (hcompact : IsCompact s)
    (hpos : 0 < intrinsicVolume s) : 0 < intrinsicVolumeReal s := by
  exact ENNReal.toReal_pos hpos.ne' (intrinsicVolume_lt_top hne hcompact).ne

/-- Conversion back to `ℝ≥0∞` is exact for a nonempty compact body's real intrinsic volume. -/
theorem ofReal_intrinsicVolumeReal {s : Set E} (hne : s.Nonempty) (hcompact : IsCompact s) :
    ENNReal.ofReal (intrinsicVolumeReal s) = intrinsicVolume s := by
  exact ENNReal.ofReal_toReal (intrinsicVolume_lt_top hne hcompact).ne

/-- Positive measure implies nonemptiness. -/
theorem nonempty_of_euclideanHausdorffMeasure_pos {k : ℕ} {s : Set E}
    (hpos : 0 < μHE[k] s) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hs
  subst s
  simpa using hpos.ne'

/-- If a compact set contained in an affine subspace has positive measure in the dimension of that
subspace, then it spans the whole affine subspace.  Convexity is not needed for this implication. -/
theorem affineSpan_eq_of_pos_euclideanHausdorffMeasure
    (A : AffineSubspace ℝ E) {s : Set E} (hcompact : IsCompact s) (hsub : s ⊆ A)
    (hpos : 0 < μHE[Module.finrank ℝ A.direction] s) :
    affineSpan ℝ s = A := by
  have hne : s.Nonempty := nonempty_of_euclideanHausdorffMeasure_pos hpos
  let B := affineSpan ℝ s
  have hBA : B ≤ A := affineSpan_le.mpr hsub
  have hdirle : B.direction ≤ A.direction := AffineSubspace.direction_le hBA
  have hdimle : Module.finrank ℝ B.direction ≤ Module.finrank ℝ A.direction :=
    Submodule.finrank_mono hdirle
  have hdimnotlt : ¬ Module.finrank ℝ B.direction < Module.finrank ℝ A.direction := by
    intro hlt
    rcases Measure.euclideanHausdorffMeasure_zero_or_top hlt s with hzero | htop
    · exact hpos.ne' hzero
    · letI : Nonempty B :=
        ⟨⟨hne.some, subset_affineSpan ℝ s hne.some_mem⟩⟩
      have hfinite : μHE[Module.finrank ℝ B.direction] s < ⊤ :=
        euclideanHausdorffMeasure_lt_top_of_isCompact_of_subset_affineSubspace
          B hcompact (subset_affineSpan ℝ s)
      exact hfinite.ne htop
  have hdimeq : Module.finrank ℝ B.direction = Module.finrank ℝ A.direction :=
    le_antisymm hdimle (Nat.le_of_not_gt hdimnotlt)
  have hdirection : B.direction = A.direction :=
    Submodule.eq_of_le_of_finrank_eq hdirle hdimeq
  exact (AffineSubspace.eq_iff_direction_eq_of_mem
    (subset_affineSpan ℝ s hne.some_mem) (hsub hne.some_mem)).mpr hdirection

/-- Dimension form of `affineSpan_eq_of_pos_euclideanHausdorffMeasure`. -/
theorem affineDim_eq_of_pos_euclideanHausdorffMeasure
    (A : AffineSubspace ℝ E) {s : Set E} (hcompact : IsCompact s) (hsub : s ⊆ A)
    (hpos : 0 < μHE[Module.finrank ℝ A.direction] s) :
    affineDim s = Module.finrank ℝ A.direction := by
  rw [affineDim, affineSpan_eq_of_pos_euclideanHausdorffMeasure A hcompact hsub hpos]

/-- A positive full-dimensional compact subset of a compact body has the same affine span. -/
theorem affineSpan_eq_of_positive_measure_subset {P Q : Set E}
    (hQcompact : IsCompact Q) (hQP : Q ⊆ P)
    (hpos : 0 < μHE[affineDim P] Q) :
    affineSpan ℝ Q = affineSpan ℝ P := by
  apply affineSpan_eq_of_pos_euclideanHausdorffMeasure (affineSpan ℝ P) hQcompact
    (hQP.trans (subset_affineSpan ℝ P))
  simpa [affineDim]

/-- Consequently, a positive full-dimensional compact subset preserves affine dimension. -/
theorem affineDim_eq_of_positive_measure_subset {P Q : Set E}
    (hQcompact : IsCompact Q) (hQP : Q ⊆ P)
    (hpos : 0 < μHE[affineDim P] Q) :
    affineDim Q = affineDim P := by
  unfold affineDim
  rw [affineSpan_eq_of_positive_measure_subset hQcompact hQP hpos]

/-- A lightweight bundle for the compact convex row bodies manipulated by the oracle. -/
structure IntrinsicBody (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  isCompact : IsCompact carrier
  convex : Convex ℝ carrier
  volume_pos : 0 < intrinsicVolume carrier

namespace IntrinsicBody

instance : SetLike (IntrinsicBody E) E where
  coe P := P.carrier
  coe_injective P Q h := by cases P; cases Q; cases h; rfl

@[simp]
theorem mem_carrier (P : IntrinsicBody E) (x : E) : x ∈ P.carrier ↔ x ∈ P :=
  Iff.rfl

theorem volume_lt_top (P : IntrinsicBody E) : intrinsicVolume P.carrier < ⊤ :=
  intrinsicVolume_lt_top P.nonempty P.isCompact

/-- Construct a body without separately reproving positivity. -/
def ofCompactConvex (carrier : Set E) (hne : carrier.Nonempty)
    (hcompact : IsCompact carrier) (hconvex : Convex ℝ carrier) : IntrinsicBody E where
  carrier := carrier
  nonempty := hne
  isCompact := hcompact
  convex := hconvex
  volume_pos := intrinsicVolume_pos_of_nonempty_convex hne hconvex

/-- The affine hull tracked implicitly by an intrinsic body. -/
def hull (P : IntrinsicBody E) : AffineSubspace ℝ E :=
  affineSpan ℝ P.carrier

/-- Affine dimension of a bundled body. -/
def dim (P : IntrinsicBody E) : ℕ :=
  affineDim P.carrier

/-- ENNReal-valued volume of a bundled body. -/
def volume (P : IntrinsicBody E) : ℝ≥0∞ :=
  intrinsicVolume P.carrier

/-- Real-valued volume of a bundled body. -/
def volumeReal (P : IntrinsicBody E) : ℝ :=
  intrinsicVolumeReal P.carrier

theorem volumeReal_pos (P : IntrinsicBody E) : 0 < P.volumeReal :=
  intrinsicVolumeReal_pos P.nonempty P.isCompact P.volume_pos

theorem carrier_subset_hull (P : IntrinsicBody E) : P.carrier ⊆ P.hull :=
  subset_affineSpan ℝ P.carrier

theorem volume_le_of_subset_closedBall (P : IntrinsicBody E) {r : ℝ}
    (hball : P.carrier ⊆ closedBall (0 : E) r) :
    P.volume ≤ ENNReal.ofReal r ^ P.dim * kappa P.dim :=
  intrinsicVolume_le_of_subset_closedBall P.nonempty hball

theorem volume_le_of_pairwise_dist_lt (P : IntrinsicBody E) {r : ℝ}
    (hdiam : ∀ x ∈ P.carrier, ∀ y ∈ P.carrier, dist x y < r) :
    P.volume ≤ ENNReal.ofReal r ^ P.dim * kappa P.dim :=
  intrinsicVolume_le_of_pairwise_dist_lt P.nonempty hdiam

end IntrinsicBody

end ZeroOrderBounds
