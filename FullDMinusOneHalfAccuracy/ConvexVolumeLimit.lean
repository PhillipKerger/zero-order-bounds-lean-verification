import FullDMinusOneHalfAccuracy.DirectionalWidth
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecificLimits.Basic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Ball containment and the volume limit in Urysohn's inequality

This file isolates the elementary limiting step used at the end of the
rotation-average proof of Urysohn's inequality.

* A uniform upper bound on the support function of a compact nonempty set in
  every unit direction puts the set in the corresponding closed ball.
* If a fixed set has volume at most that of every positive enlargement of a
  radius-`r` ball, then it has volume at most that of the radius-`r` ball.

The second statement is proved directly from continuity from above for
Lebesgue measure, using the decreasing sequence of radii
`r + 1 / (n + 1)`.  Thus it does not assume any general Hausdorff-continuity
theorem for convex-body volume.
-/

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Pointwise Topology

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A compact nonempty set whose upper support is at most `r` in every unit
direction is contained in the radius-`r` ball centered at the origin.

The `Nontrivial E` assumption is necessary: in the zero-dimensional space
there are no unit directions, so the support hypothesis would be vacuous.
-/
theorem subset_closedBall_of_directionalSupportSup_le [Nontrivial E]
    {s : Set E} (hs : IsCompact s) (hne : s.Nonempty) {r : ℝ}
    (hsupport : ∀ θ : E, ‖θ‖ = 1 → directionalSupportSup s θ ≤ r) :
    s ⊆ closedBall (0 : E) r := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := exists_ne 0
    let θ : E := ‖v‖⁻¹ • v
    have hθ : ‖θ‖ = 1 := norm_smul_inv_norm hv
    obtain ⟨p, hp, hsup, hpmax⟩ :=
      ZeroOrderBounds.IsCompact.exists_directionalSupportSup_eq hs hne θ
    have hzero : inner ℝ θ (0 : E) ≤ directionalSupportSup s θ := by
      rw [hsup]
      exact hpmax 0 hx
    have hr : 0 ≤ r := by
      simpa using hzero.trans (hsupport θ hθ)
    simpa [mem_closedBall] using hr
  · let θ : E := ‖x‖⁻¹ • x
    have hθ : ‖θ‖ = 1 := norm_smul_inv_norm hx0
    obtain ⟨p, hp, hsup, hpmax⟩ :=
      ZeroOrderBounds.IsCompact.exists_directionalSupportSup_eq hs hne θ
    have hxle : inner ℝ θ x ≤ r := by
      calc
        inner ℝ θ x ≤ inner ℝ θ p := hpmax x hx
        _ = directionalSupportSup s θ := hsup.symm
        _ ≤ r := hsupport θ hθ
    have hinner : inner ℝ θ x = ‖x‖ := by
      simp only [θ, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [inv_mul_eq_div, sq,
        mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hx0)]
    simpa [mem_closedBall, dist_zero_right, hinner] using hxle

/-- A fixed volume lower bound for every positive enlargement of a closed
ball also holds for the limiting closed ball.

This is the exact order-closed endpoint needed in the rotation-average proof
of Urysohn's inequality.  It works for an arbitrary set `K`; no convexity or
measurability hypothesis on `K` is needed.
-/
theorem volume_le_closedBall_of_forall_pos
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} {r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      volume K ≤ volume (closedBall (0 : E) (r + ε))) :
    volume K ≤ volume (closedBall (0 : E) r) := by
  let B : ℕ → Set E := fun n ↦
    closedBall (0 : E) (r + 1 / ((n : ℝ) + 1))
  have hBanti : Antitone B := by
    intro n m hnm
    apply closedBall_subset_closedBall
    gcongr
  have hBmeas : ∀ n, NullMeasurableSet (B n) volume := by
    intro n
    exact measurableSet_closedBall.nullMeasurableSet
  have hBfin : ∃ n, volume (B n) ≠ ⊤ := by
    exact ⟨0, measure_closedBall_lt_top.ne⟩
  have hBinter : (⋂ n, B n) = closedBall (0 : E) r := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxall : ∀ n : ℕ,
          dist x 0 ≤ r + 1 / ((n : ℝ) + 1) := by
        intro n
        exact mem_closedBall.mp (mem_iInter.mp hx n)
      have hlim : Tendsto
          (fun n : ℕ ↦ r + 1 / ((n : ℝ) + 1)) atTop (nhds r) := by
        convert! (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0)))
        simp
      exact mem_closedBall.mpr (ge_of_tendsto' hlim hxall)
    · intro x hx
      apply mem_iInter.mpr
      intro n
      change x ∈ closedBall (0 : E) (r + 1 / ((n : ℝ) + 1))
      have hnpos : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      exact closedBall_subset_closedBall (le_add_of_nonneg_right hnpos) hx
  calc
    volume K ≤ ⨅ n, volume (B n) := by
      apply le_iInf
      intro n
      exact h (1 / ((n : ℝ) + 1)) (by positivity)
    _ = volume (⋂ n, B n) :=
      (hBanti.measure_iInter hBmeas hBfin).symm
    _ = volume (closedBall (0 : E) r) := by rw [hBinter]

/-- Set-theoretic sandwich form of `volume_le_closedBall_of_forall_pos`.
For each positive `ε`, the intermediate approximant may be a different set.
-/
theorem volume_le_closedBall_of_approximate_supersets
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} {r : ℝ} (A : ℝ → Set E)
    (hvolume : ∀ ε : ℝ, 0 < ε → volume K ≤ volume (A ε))
    (hball : ∀ ε : ℝ, 0 < ε →
      A ε ⊆ closedBall (0 : E) (r + ε)) :
    volume K ≤ volume (closedBall (0 : E) r) := by
  apply volume_le_closedBall_of_forall_pos
  intro ε hε
  exact (hvolume ε hε).trans (measure_mono (hball ε hε))

/-- Support-function form of the approximate-volume endpoint.  This is a
convenient interface for finite rotation averages: Brunn--Minkowski supplies
`hvolume`, while uniform convergence of support functions supplies
`hsupport`.
-/
theorem volume_le_closedBall_of_approximate_support_bounds
    [Nontrivial E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K : Set E} {r : ℝ} (A : ℝ → Set E)
    (hcompact : ∀ ε : ℝ, 0 < ε → IsCompact (A ε))
    (hnonempty : ∀ ε : ℝ, 0 < ε → (A ε).Nonempty)
    (hvolume : ∀ ε : ℝ, 0 < ε → volume K ≤ volume (A ε))
    (hsupport : ∀ ε : ℝ, 0 < ε → ∀ θ : E, ‖θ‖ = 1 →
      directionalSupportSup (A ε) θ ≤ r + ε) :
    volume K ≤ volume (closedBall (0 : E) r) := by
  apply volume_le_closedBall_of_approximate_supersets A hvolume
  intro ε hε
  exact subset_closedBall_of_directionalSupportSup_le
    (hcompact ε hε) (hnonempty ε hε) (hsupport ε hε)

end ZeroOrderBounds.AccuracyImprovement
