import FullDMinusOneHalfAccuracy.CommonDirection

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# From intrinsic row width to ambient row width

This file isolates the exact interface between Urysohn's intrinsic estimate
and the common-direction endgame.  A good row has direction-space dimension
at least `24m/25`; spherical projection therefore loses at most a factor two.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

/-- Intrinsic mean width of a positive-dimensional row body.  The positivity
proof supplies the nontriviality instance required to normalize its sphere. -/
def positiveIntrinsicMeanWidth {m : ℕ} (P : RowBody m)
    (hdim_pos : 0 < P.dim) : ℝ := by
  letI : Nontrivial P.body.directionSpan :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_directionSpan_eq_dim]
      exact hdim_pos)
  exact intrinsicMeanWidth P.body P.body.directionSpan

/-- A positive-dimensional row whose direction space occupies at least half
of the ambient row space loses at most a factor two when its intrinsic mean
width is viewed on the ambient sphere. -/
theorem half_intrinsicMeanWidth_le_sphericalMeanWidth
    {m : ℕ} [NeZero m] (P : RowBody m)
    (hdim_pos : 0 < P.dim) (hdim_half : m ≤ 2 * P.dim)
    {w : ℝ} (hw₀ : 0 ≤ w)
    (hw : w ≤ positiveIntrinsicMeanWidth P hdim_pos) :
    w / 2 ≤ sphericalMeanWidth (P : Set (RowSpace m)) := by
  letI : Nontrivial P.body.directionSpan :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_directionSpan_eq_dim]
      exact hdim_pos)
  change w ≤ intrinsicMeanWidth P.body P.body.directionSpan at hw
  change w / 2 ≤ sphericalMeanWidth P.body.carrier
  rw [sphericalMeanWidth_carrier_eq_ambientMeanWidth P.body]
  apply half_le_ambientMeanWidth_of_one_le_intrinsic
    P.body P.body.directionSpan rfl
  · simpa [RowBody.dim] using hdim_half
  · exact hw₀
  · exact hw

/-- The `24/25` dimension certificate produced by `ManyGoodRows` is more
than enough for the half-dimensional projection bound. -/
theorem tau_half_le_sphericalMeanWidth_of_high_dimension
    {m : ℕ} [NeZero m] (P : RowBody m)
    (hdim : 24 * m ≤ 25 * P.dim) (hdim_pos : 0 < P.dim)
    (hw : tau m ≤ positiveIntrinsicMeanWidth P hdim_pos) :
    tau m / 2 ≤ sphericalMeanWidth (P : Set (RowSpace m)) := by
  apply half_intrinsicMeanWidth_le_sphericalMeanWidth P hdim_pos
  · omega
  · exact (tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))).le
  · exact hw

/-- Family form used directly after the many-good-rows theorem. -/
theorem row_meanWidths_of_intrinsic_meanWidths
    {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (G : Finset (Fin m))
    (hdim : ∀ i ∈ G, 24 * m ≤ 25 * (rows i).dim)
    (hdim_pos : ∀ i ∈ G, 0 < (rows i).dim)
    (hwidth : ∀ i, ∀ hi : i ∈ G,
      tau m ≤ positiveIntrinsicMeanWidth (rows i) (hdim_pos i hi)) :
    ∀ i ∈ G,
      tau m / 2 ≤ sphericalMeanWidth (rows i : Set (RowSpace m)) := by
  intro i hi
  exact tau_half_le_sphericalMeanWidth_of_high_dimension (rows i)
    (hdim i hi) (hdim_pos i hi) (hwidth i hi)

end ZeroOrderBounds.AccuracyImprovement
