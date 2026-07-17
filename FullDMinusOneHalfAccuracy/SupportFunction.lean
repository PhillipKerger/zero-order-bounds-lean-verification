import FullDMinusOneHalfAccuracy.MinkowskiWidth

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Support functions and difference bodies

Urysohn's inequality is most naturally proved after replacing a body `K` by
its difference body `K + (-K)`.  Its support function is exactly the full
directional width of `K`.  This file proves that identity directly from
compact extrema, together with the Minkowski algebra of upper support.
-/

noncomputable section

open Set
open scoped Pointwise

namespace ZeroOrderBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A specified maximizing point computes upper directional support. -/
theorem directionalSupportSup_eq_inner_of_max {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) (theta p : E)
    (hp : p ∈ s)
    (hpmax : ∀ x ∈ s, inner ℝ theta x ≤ inner ℝ theta p) :
    directionalSupportSup s theta = inner ℝ theta p := by
  obtain ⟨q, hq, hsup, hqmax⟩ :=
    IsCompact.exists_directionalSupportSup_eq hs hne theta
  rw [hsup]
  exact le_antisymm (hpmax q hq) (hqmax p hp)

/-- Upper support is additive under Minkowski addition. -/
theorem directionalSupportSup_add {s t : Set E}
    (hs : IsCompact s) (hneS : s.Nonempty)
    (ht : IsCompact t) (hneT : t.Nonempty) (theta : E) :
    directionalSupportSup (s + t) theta =
      directionalSupportSup s theta + directionalSupportSup t theta := by
  obtain ⟨p, hp, hsp, hpmax⟩ :=
    IsCompact.exists_directionalSupportSup_eq hs hneS theta
  obtain ⟨q, hq, hsq, hqmax⟩ :=
    IsCompact.exists_directionalSupportSup_eq ht hneT theta
  have hpq : p + q ∈ s + t := Set.mem_add.mpr ⟨p, hp, q, hq, rfl⟩
  rw [directionalSupportSup_eq_inner_of_max (hs.add ht) (hneS.add hneT)
    theta (p + q) hpq]
  · simp only [inner_add_right, hsp, hsq]
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    simp only [inner_add_right]
    exact add_le_add (hpmax x hx) (hqmax y hy)

/-- Upper support is homogeneous under nonnegative dilation. -/
theorem directionalSupportSup_smul_set_of_nonneg {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) (theta : E)
    {c : ℝ} (hc : 0 ≤ c) :
    directionalSupportSup (c • s) theta = c * directionalSupportSup s theta := by
  obtain ⟨p, hp, hsp, hpmax⟩ :=
    IsCompact.exists_directionalSupportSup_eq hs hne theta
  have hcp : c • p ∈ c • s := Set.mem_smul_set.mpr ⟨p, hp, rfl⟩
  rw [directionalSupportSup_eq_inner_of_max (hs.smul c) hne.smul_set
    theta (c • p) hcp]
  · simp only [real_inner_smul_right, hsp]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hz
    simp only [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hpmax x hx) hc

end ZeroOrderBounds

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The centrally symmetric difference body `K-K`. -/
def convexBodyDifference (K : ConvexBody E) : ConvexBody E :=
  K + (-1 : ℝ) • K

@[simp]
theorem coe_convexBodyDifference (K : ConvexBody E) :
    (convexBodyDifference K : Set E) =
      (K : Set E) + (-1 : ℝ) • (K : Set E) :=
  rfl

/-- The difference body is symmetric about the origin. -/
theorem convexBodyDifference_neg_mem (K : ConvexBody E)
    {z : E} (hz : z ∈ convexBodyDifference K) :
    -z ∈ convexBodyDifference K := by
  change z ∈ (convexBodyDifference K : Set E) at hz
  change -z ∈ (convexBodyDifference K : Set E)
  rw [coe_convexBodyDifference] at hz ⊢
  obtain ⟨x, hx, ny, hny, hxy⟩ := Set.mem_add.mp hz
  obtain ⟨y, hy, hnyEq⟩ := Set.mem_smul_set.mp hny
  subst ny
  have hnegx : (-1 : ℝ) • x ∈ (-1 : ℝ) • (K : Set E) :=
    Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
  apply Set.mem_add.mpr
  refine ⟨y, hy, (-1 : ℝ) • x, hnegx, ?_⟩
  rw [← hxy]
  simp

/-- The support function of `K-K` is exactly the full width of `K`. -/
theorem directionalSupportSup_convexBodyDifference (K : ConvexBody E)
    (theta : E) :
    directionalSupportSup (convexBodyDifference K : Set E) theta =
      directionalWidth (K : Set E) theta := by
  obtain ⟨p, hp, q, hq, hpmax, hqmin, hwidth⟩ :=
    IsCompact.exists_directionalWidth_eq K.isCompact K.nonempty theta
  have hpq : p + (-1 : ℝ) • q ∈
      (K : Set E) + (-1 : ℝ) • (K : Set E) := by
    apply Set.mem_add.mpr
    exact ⟨p, hp, (-1 : ℝ) • q,
      Set.mem_smul_set.mpr ⟨q, hq, rfl⟩, rfl⟩
  rw [coe_convexBodyDifference,
    directionalSupportSup_eq_inner_of_max
      (K.isCompact.add (K.isCompact.smul (-1 : ℝ)))
      (K.nonempty.add K.nonempty.smul_set) theta
      (p + (-1 : ℝ) • q) hpq]
  · rw [hwidth]
    simp only [inner_add_right, real_inner_smul_right]
    ring
  · intro z hz
    obtain ⟨x, hx, ny, hny, rfl⟩ := Set.mem_add.mp hz
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hny
    simp only [inner_add_right, real_inner_smul_right]
    linarith [hpmax x hx, hqmin y hy]

end ZeroOrderBounds.AccuracyImprovement
