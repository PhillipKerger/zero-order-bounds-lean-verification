import FullDMinusOneHalfAccuracy.BrunnMinkowski
import Mathlib.MeasureTheory.Integral.Prod

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Vertical slices for the Brunn--Minkowski induction

This file is the geometric half of the standard induction-on-dimension proof
of Brunn--Minkowski.  It proves the exact Cavalieri formula for compact sets in
`ℝ × V`, packages every nonempty convex slice as a convex body in `V`, and
proves the load-bearing inclusion of weighted Minkowski sums of slices.

The remaining analytic half is the one-dimensional
Borell--Brascamp--Lieb inequality for the slice-volume functions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The vertical slice of `S ⊆ ℝ × V` at first coordinate `x`. -/
def verticalSlice (S : Set (ℝ × V)) (x : ℝ) : Set V :=
  (fun v : V ↦ (x, v)) ⁻¹' S

@[simp]
theorem mem_verticalSlice {S : Set (ℝ × V)} {x : ℝ} {v : V} :
    v ∈ verticalSlice S x ↔ (x, v) ∈ S :=
  Iff.rfl

/-- A vertical slice is the second-coordinate image of a closed fiber. -/
theorem verticalSlice_eq_snd_image (S : Set (ℝ × V)) (x : ℝ) :
    verticalSlice S x =
      Prod.snd '' (S ∩ ({x} ×ˢ (Set.univ : Set V))) := by
  ext v
  constructor
  · intro hv
    exact ⟨(x, v), ⟨hv, by simp⟩, rfl⟩
  · rintro ⟨p, ⟨hpS, hpfiber⟩, rfl⟩
    have hpfirst : p.1 = x := by simpa using hpfiber.1
    change (x, p.2) ∈ S
    convert hpS using 1
    ext <;> simp [hpfirst]

/-- Slices of compact sets are compact. -/
theorem isCompact_verticalSlice {S : Set (ℝ × V)}
    (hS : IsCompact S) (x : ℝ) :
    IsCompact (verticalSlice S x) := by
  rw [verticalSlice_eq_snd_image]
  apply IsCompact.image
  · exact hS.inter_right (isClosed_singleton.prod isClosed_univ)
  · fun_prop

/-- Slices of convex sets are convex. -/
theorem convex_verticalSlice {S : Set (ℝ × V)}
    (hS : Convex ℝ S) (x : ℝ) :
    Convex ℝ (verticalSlice S x) := by
  intro a ha b hb u v hu hv huv
  change (x, u • a + v • b) ∈ S
  have hpair : (x, u • a + v • b) =
      u • (x, a) + v • (x, b) := by
    ext
    · dsimp
      rw [← add_mul, huv, one_mul]
    · simp
  rw [hpair]
  exact hS ha hb hu hv huv

/-- Package a nonempty slice of a convex body as a convex body in one lower
coordinate space. -/
def verticalSliceBody (K : ConvexBody (ℝ × V)) (x : ℝ)
    (hne : (verticalSlice (K : Set (ℝ × V)) x).Nonempty) :
    ConvexBody V where
  carrier := verticalSlice (K : Set (ℝ × V)) x
  convex' := convex_verticalSlice K.convex x
  isCompact' := isCompact_verticalSlice K.isCompact x
  nonempty' := hne

@[simp]
theorem coe_verticalSliceBody (K : ConvexBody (ℝ × V)) (x : ℝ)
    (hne : (verticalSlice (K : Set (ℝ × V)) x).Nonempty) :
    (verticalSliceBody K x hne : Set V) =
      verticalSlice (K : Set (ℝ × V)) x :=
  rfl

/-- Cavalieri/Fubini formula for a compact set in a product Euclidean space. -/
theorem volume_eq_lintegral_verticalSlice {S : Set (ℝ × V)}
    (hS : IsCompact S) :
    volume S = ∫⁻ x : ℝ, volume (verticalSlice S x) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply hS.measurableSet]
  rfl

/-- Unweighted sums of slices lie in the corresponding slice of the
Minkowski sum. -/
theorem add_verticalSlice_subset_verticalSlice_add
    {A B : Set (ℝ × V)} (x y : ℝ) :
    verticalSlice A x + verticalSlice B y ⊆
      verticalSlice (A + B) (x + y) := by
  intro z hz
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hz
  apply Set.mem_add.mpr
  refine ⟨(x, a), ha, (y, b), hb, ?_⟩
  ext
  · simp
  · exact hab

/-- The load-bearing slice inclusion for Minkowski interpolation. -/
theorem weighted_verticalSlice_subset
    {A B : Set (ℝ × V)} (t x y : ℝ) :
    (1 - t) • verticalSlice A x + t • verticalSlice B y ⊆
      verticalSlice ((1 - t) • A + t • B) ((1 - t) * x + t * y) := by
  intro z hz
  obtain ⟨sa, hsa, sb, hsb, hzsum⟩ := Set.mem_add.mp hz
  obtain ⟨a, ha, hsaEq⟩ := Set.mem_smul_set.mp hsa
  obtain ⟨b, hb, hsbEq⟩ := Set.mem_smul_set.mp hsb
  apply Set.mem_add.mpr
  refine ⟨(1 - t) • (x, a), Set.mem_smul_set.mpr ⟨(x, a), ha, rfl⟩,
    t • (y, b), Set.mem_smul_set.mpr ⟨(y, b), hb, rfl⟩, ?_⟩
  subst sa
  subst sb
  ext
  · simp
  · exact hzsum

/-- Bundled-body form of the weighted slice inclusion. -/
theorem weighted_verticalSliceBody_subset
    (K L : ConvexBody (ℝ × V)) {t x y : ℝ}
    (hKx : (verticalSlice (K : Set (ℝ × V)) x).Nonempty)
    (hLy : (verticalSlice (L : Set (ℝ × V)) y).Nonempty) :
    (↑((1 - t) • verticalSliceBody K x hKx +
        t • verticalSliceBody L y hLy : ConvexBody V) : Set V) ⊆
      verticalSlice
        ((1 - t) • K + t • L).carrier
        ((1 - t) * x + t * y) := by
  change (1 - t) • verticalSlice (K : Set (ℝ × V)) x +
      t • verticalSlice (L : Set (ℝ × V)) y ⊆ _
  exact weighted_verticalSlice_subset t x y

end ZeroOrderBounds.AccuracyImprovement
