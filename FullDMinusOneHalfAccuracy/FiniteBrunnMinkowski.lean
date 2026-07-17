import FullDMinusOneHalfAccuracy.BrunnMinkowski
import FullDMinusOneHalfAccuracy.RotationAction
import FullDMinusOneHalfAccuracy.SupportFunction

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Finite consequences of binary Brunn--Minkowski

Urysohn's rotation argument approximates a Haar average by a finite weighted
Minkowski sum.  This module isolates the purely algebraic passage from the
binary midpoint Brunn--Minkowski inequality to that finite form.  The general
binary theorem is retained as an explicit premise until it is discharged by
the analytic Brunn--Minkowski development.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In positive dimension, comparison of homogeneous volume roots is
equivalent to comparison of real volumes. -/
theorem convexBodyVolumeRoot_le_iff
    (hdim : Module.finrank ℝ E ≠ 0) (K L : ConvexBody E) :
    convexBodyVolumeRoot K ≤ convexBodyVolumeRoot L ↔
      convexBodyVolumeReal K ≤ convexBodyVolumeReal L := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot]
  exact Real.rpow_le_rpow_iff
    (convexBodyVolumeReal_nonneg K) (convexBodyVolumeReal_nonneg L)
    (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hdim))

/-- The ENNReal volume comparison corresponding to a volume-root comparison. -/
theorem volume_le_volume_of_convexBodyVolumeRoot_le
    (hdim : Module.finrank ℝ E ≠ 0) {K L : ConvexBody E}
    (hroot : convexBodyVolumeRoot K ≤ convexBodyVolumeRoot L) :
    volume (K : Set E) ≤ volume (L : Set E) := by
  apply (ENNReal.toReal_le_toReal K.isCompact.measure_lt_top.ne
    L.isCompact.measure_lt_top.ne).mp
  exact (convexBodyVolumeRoot_le_iff hdim K L).mp hroot

/-- Reflection through the origin preserves real Euclidean volume. -/
theorem convexBodyVolumeReal_neg_one_smul (K : ConvexBody E) :
    convexBodyVolumeReal ((-1 : ℝ) • K) = convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal, ConvexBody.coe_smul,
    Measure.addHaar_smul]
  norm_num

/-- Reflection through the origin preserves the homogeneous volume root. -/
theorem convexBodyVolumeRoot_neg_one_smul (K : ConvexBody E) :
    convexBodyVolumeRoot ((-1 : ℝ) • K) = convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_neg_one_smul]

/-- Orthogonal matrix rotations preserve the real volume used in
Brunn--Minkowski. -/
theorem convexBodyVolumeReal_orthogonalRotate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix.orthogonalGroup n ℝ)
    (K : ConvexBody (EuclideanSpace ℝ n)) :
    convexBodyVolumeReal (orthogonalRotate A K) = convexBodyVolumeReal K := by
  rw [convexBodyVolumeReal, convexBodyVolumeReal, volume_orthogonalRotate]

/-- Orthogonal matrix rotations preserve homogeneous volume root. -/
theorem convexBodyVolumeRoot_orthogonalRotate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix.orthogonalGroup n ℝ)
    (K : ConvexBody (EuclideanSpace ℝ n)) :
    convexBodyVolumeRoot (orthogonalRotate A K) = convexBodyVolumeRoot K := by
  rw [convexBodyVolumeRoot, convexBodyVolumeRoot,
    convexBodyVolumeReal_orthogonalRotate]

/-- Binary midpoint Brunn--Minkowski implies superadditivity of the homogeneous
volume root under an unweighted Minkowski sum. -/
theorem convexBodyVolumeRoot_add_superadditive
    (hdim : Module.finrank ℝ E ≠ 0)
    (hBM : ∀ K L : ConvexBody E, BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K L : ConvexBody E) :
    convexBodyVolumeRoot K + convexBodyVolumeRoot L ≤
      convexBodyVolumeRoot (K + L) := by
  have hmid := hBM K L
  have hbody : weightedMinkowski (1 / 2 : ℝ) K L =
      (1 / 2 : ℝ) • (K + L) := by
    simp only [weightedMinkowski]
    norm_num
  rw [BrunnMinkowskiAt, hbody,
    convexBodyVolumeRoot_smul_of_nonneg (K + L) hdim (by norm_num)] at hmid
  nlinarith

/-- Brunn--Minkowski makes the difference body's volume root at least twice
that of the original body. -/
theorem two_mul_convexBodyVolumeRoot_le_difference
    (hdim : Module.finrank ℝ E ≠ 0)
    (hBM : ∀ K L : ConvexBody E, BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    (K : ConvexBody E) :
    2 * convexBodyVolumeRoot K ≤
      convexBodyVolumeRoot (convexBodyDifference K) := by
  have hsum := convexBodyVolumeRoot_add_superadditive hdim hBM K ((-1 : ℝ) • K)
  rw [convexBodyVolumeRoot_neg_one_smul] at hsum
  simpa [convexBodyDifference, two_mul] using hsum

/-- Finite superadditivity of the volume root. -/
theorem sum_convexBodyVolumeRoot_le
    (hdim : Module.finrank ℝ E ≠ 0)
    (hBM : ∀ K L : ConvexBody E, BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    {ι : Type*} (s : Finset ι) (K : ι → ConvexBody E) :
    (∑ i ∈ s, convexBodyVolumeRoot (K i)) ≤
      convexBodyVolumeRoot (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact convexBodyVolumeRoot_nonneg 0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (add_le_add_right ih _).trans
        (convexBodyVolumeRoot_add_superadditive hdim hBM _ _)

/-- Weighted finite Brunn--Minkowski.  No normalization of the weights is
needed: homogeneity puts the weight on each volume root automatically. -/
theorem sum_weighted_convexBodyVolumeRoot_le
    (hdim : Module.finrank ℝ E ≠ 0)
    (hBM : ∀ K L : ConvexBody E, BrunnMinkowskiAt (1 / 2 : ℝ) K L)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (K : ι → ConvexBody E)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * convexBodyVolumeRoot (K i)) ≤
      convexBodyVolumeRoot (∑ i ∈ s, w i • K i) := by
  have hfinite := sum_convexBodyVolumeRoot_le hdim hBM s
    (fun i => w i • K i)
  calc
    (∑ i ∈ s, w i * convexBodyVolumeRoot (K i)) =
        ∑ i ∈ s, convexBodyVolumeRoot (w i • K i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [convexBodyVolumeRoot_smul_of_nonneg (K i) hdim (hw i hi)]
    _ ≤ convexBodyVolumeRoot (∑ i ∈ s, w i • K i) := hfinite

end ZeroOrderBounds.AccuracyImprovement
