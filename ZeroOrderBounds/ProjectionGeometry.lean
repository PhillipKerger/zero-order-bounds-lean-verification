import ZeroOrderBounds.Covariance
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Minimum-norm barycentric geometry

The hard slopes are combined using the standard probability simplex.  We apply
the Hilbert projection theorem to the image of that simplex under the
barycentric linear map.  This produces the minimum-norm slope combination and
its variational inequality, from which the optimizer and quadratic growth
estimate follow.
-/

noncomputable section

open scoped BigOperators
open Set

namespace ZeroOrderBounds

/-- Probability weights on the `m` hard slopes. -/
abbrev WeightSimplex (m : ℕ) := stdSimplex ℝ (Fin m)

/-- View a family of real weights as a vector in the Euclidean row space. -/
def weightVector {m : ℕ} (w : Fin m → ℝ) : RowSpace m :=
  WithLp.toLp 2 w

@[simp]
theorem weightVector_apply {m : ℕ} (w : Fin m → ℝ) (i : Fin m) :
    weightVector w i = w i :=
  rfl

/-- The linear map taking weights to the corresponding combination of slopes. -/
def barycentricMap {m : ℕ} (W : RowMatrix m) :
    (Fin m → ℝ) →L[ℝ] QuerySpace m :=
  LinearMap.toContinuousLinearMap
    (∑ i, (LinearMap.proj i).smulRight (slope W i))

@[simp]
theorem barycentricMap_apply {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ) :
    barycentricMap W w = ∑ i, w i • slope W i := by
  simp [barycentricMap]

/-- Block formula for a barycentric slope combination. -/
theorem barycentricMap_eq_joinBlocks {m : ℕ} (W : RowMatrix m) (w : Fin m → ℝ) :
    barycentricMap W w =
      joinBlocks (a • weightVector w) (∑ i, w i • W i) := by
  ext i
  cases i with
  | inl j =>
      simp [barycentricMap_apply, slope, Finset.sum_apply, weightVector,
        mul_comm]
  | inr j =>
      simp [barycentricMap_apply, slope, Finset.sum_apply, weightVector]

/-- Coordinate formula for the first block of a barycentric combination. -/
@[simp]
theorem firstBlock_barycentricMap_apply {m : ℕ} (W : RowMatrix m)
    (w : Fin m → ℝ) (j : Fin m) :
    firstBlock (barycentricMap W w) j = a * w j := by
  rw [barycentricMap_eq_joinBlocks]
  simp [weightVector]

/-- The barycentric map is injective because its first block is `a` times the weights. -/
theorem barycentricMap_injective {m : ℕ} (W : RowMatrix m) :
    Function.Injective (barycentricMap W) := by
  intro w u h
  funext j
  have hj := congrArg (fun q : QuerySpace m ↦ firstBlock q j) h
  simp only [firstBlock_barycentricMap_apply] at hj
  nlinarith [a_pos]

/-- All barycentric combinations of the slopes. -/
def barycentricSet {m : ℕ} (W : RowMatrix m) : Set (QuerySpace m) :=
  barycentricMap W '' stdSimplex ℝ (Fin m)

/-- Existence of simplex weights satisfying the minimum-norm projection inequality. -/
theorem exists_minWeights {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ∃ w : WeightSimplex m,
      ∀ u : WeightSimplex m,
        0 ≤ inner ℝ (barycentricMap W w)
          (barycentricMap W u - barycentricMap W w) := by
  let P := barycentricMap W
  let K : Set (QuerySpace m) := P '' stdSimplex ℝ (Fin m)
  have hKne : K.Nonempty :=
    ⟨P stdSimplex.barycenter, stdSimplex.barycenter,
      stdSimplex.barycenter.2, rfl⟩
  have hKcompact : IsCompact K :=
    (isCompact_stdSimplex ℝ (Fin m)).image P.continuous
  have hKconvex : Convex ℝ K :=
    (convex_stdSimplex ℝ (Fin m)).linear_image P.toLinearMap
  obtain ⟨p, hp, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hKne hKcompact.isComplete hKconvex 0
  have hp' := hp
  obtain ⟨w, hw, rfl⟩ := hp
  refine ⟨⟨w, hw⟩, ?_⟩
  have hproj :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconvex hp').mp hmin
  intro u
  change 0 ≤ inner ℝ (P w) (P u - P w)
  simpa [K] using hproj (P u) ⟨u, u.2, rfl⟩

/-- The uniquely selected minimum-norm simplex weights. -/
def minWeights {m : ℕ} [NeZero m] (W : RowMatrix m) : WeightSimplex m :=
  Classical.choose (exists_minWeights W)

/-- The selected weights belong to the standard probability simplex. -/
theorem minWeights_mem_stdSimplex {m : ℕ} [NeZero m] (W : RowMatrix m) :
    (minWeights W : Fin m → ℝ) ∈ stdSimplex ℝ (Fin m) :=
  (minWeights W).property

/-- Variational inequality for the selected minimum weights. -/
theorem minWeights_projection {m : ℕ} [NeZero m] (W : RowMatrix m)
    (u : WeightSimplex m) :
    0 ≤ inner ℝ (barycentricMap W (minWeights W))
      (barycentricMap W u - barycentricMap W (minWeights W)) :=
  Classical.choose_spec (exists_minWeights W) u

/-- The minimum-norm barycentric combination of the hard slopes. -/
def minPoint {m : ℕ} [NeZero m] (W : RowMatrix m) : QuerySpace m :=
  barycentricMap W (minWeights W)

/-- Barycentric identity for the selected minimum point. -/
@[simp]
theorem minPoint_eq_barycentricMap {m : ℕ} [NeZero m] (W : RowMatrix m) :
    minPoint W = barycentricMap W (minWeights W) :=
  rfl

/-- The selected minimum point lies in the image of the probability simplex. -/
theorem minPoint_mem_barycentricSet {m : ℕ} [NeZero m] (W : RowMatrix m) :
    minPoint W ∈ barycentricSet W :=
  ⟨minWeights W, minWeights_mem_stdSimplex W, rfl⟩

/-- Projection inequality for the minimum-norm point. -/
theorem minPoint_projection {m : ℕ} [NeZero m] (W : RowMatrix m)
    (u : WeightSimplex m) :
    0 ≤ inner ℝ (minPoint W) (barycentricMap W u - minPoint W) := by
  exact minWeights_projection W u

/-- Every simplex barycentric combination has first-block coordinate sum `a`. -/
theorem coordinateSum_barycentricMap {m : ℕ} (W : RowMatrix m)
    (w : WeightSimplex m) :
    coordinateSum (barycentricMap W w) = a := by
  simp_rw [coordinateSum, firstBlock_barycentricMap_apply]
  rw [← Finset.mul_sum]
  calc
    a * ∑ i, w i = a * 1 := congrArg (fun x : ℝ ↦ a * x) w.2.2
    _ = a := mul_one a

/-- In particular, the selected minimum-norm point has coordinate sum `a`. -/
@[simp]
theorem coordinateSum_minPoint {m : ℕ} [NeZero m] (W : RowMatrix m) :
    coordinateSum (minPoint W) = a := by
  exact coordinateSum_barycentricMap W (minWeights W)

/-- The minimum-norm point is bounded away from zero. -/
theorem a_div_sqrt_le_norm_minPoint {m : ℕ} [NeZero m] (W : RowMatrix m) :
    a / Real.sqrt (m : ℝ) ≤ ‖minPoint W‖ := by
  have hmnat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmnat
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hsum := abs_coordinateSum_le (minPoint W)
  rw [coordinateSum_minPoint, abs_of_pos a_pos] at hsum
  exact (div_le_iff₀ hsqrt).2 (by simpa [mul_comm] using hsum)

/-- The minimum-norm point is nonzero. -/
theorem minPoint_ne_zero {m : ℕ} [NeZero m] (W : RowMatrix m) :
    minPoint W ≠ 0 := by
  have hmnat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmnat
  have hpos : 0 < ‖minPoint W‖ :=
    lt_of_lt_of_le (div_pos a_pos (Real.sqrt_pos.2 hm))
      (a_div_sqrt_le_norm_minPoint W)
  exact norm_pos_iff.mp hpos

/-- The selected point has no larger norm than any barycentric combination. -/
theorem norm_minPoint_le {m : ℕ} [NeZero m] (W : RowMatrix m)
    (u : WeightSimplex m) :
    ‖minPoint W‖ ≤ ‖barycentricMap W u‖ := by
  have hproj := minPoint_projection W u
  have hinner : ‖minPoint W‖ ^ 2 ≤
      inner ℝ (minPoint W) (barycentricMap W u) := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [inner_sub_right] using hproj
  have hcs := real_inner_le_norm (minPoint W) (barycentricMap W u)
  nlinarith [norm_nonneg (minPoint W), norm_nonneg (barycentricMap W u)]

/-- A competitor whose norm is no larger than the selected point has the same weights. -/
theorem minWeights_unique_of_norm_le {m : ℕ} [NeZero m] (W : RowMatrix m)
    (u : WeightSimplex m)
    (hu : ‖barycentricMap W u‖ ≤ ‖minPoint W‖) :
    u = minWeights W := by
  let p := minPoint W
  let q := barycentricMap W u
  have hproj : 0 ≤ inner ℝ p (q - p) := minPoint_projection W u
  have hnormsq : ‖q‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    nlinarith [norm_nonneg p, norm_nonneg q]
  have hadd := norm_add_sq_real p (q - p)
  have hdecomp : ‖q‖ ^ 2 =
      ‖p‖ ^ 2 + 2 * inner ℝ p (q - p) + ‖q - p‖ ^ 2 := by
    simpa using hadd
  have hdist : ‖q - p‖ = 0 := by
    nlinarith [sq_nonneg ‖q - p‖, norm_nonneg (q - p)]
  have hpq : q = p := sub_eq_zero.mp (norm_eq_zero.mp hdist)
  apply Subtype.ext
  exact barycentricMap_injective W hpq

/-- The selected weights are the unique minimizer of the barycentric norm. -/
theorem minWeights_unique {m : ℕ} [NeZero m] (W : RowMatrix m)
    (u : WeightSimplex m)
    (hu : ∀ v : WeightSimplex m,
      ‖barycentricMap W u‖ ≤ ‖barycentricMap W v‖) :
    u = minWeights W :=
  minWeights_unique_of_norm_le W u (by simpa [minPoint] using hu (minWeights W))

/-- Every coordinate of the simplex barycenter is `1 / m`. -/
@[simp]
theorem barycenter_weight_apply {m : ℕ} [NeZero m] (i : Fin m) :
    (stdSimplex.barycenter : WeightSimplex m) i = (m : ℝ)⁻¹ := by
  change (stdSimplex.barycenter : WeightSimplex m).val i = (m : ℝ)⁻¹
  calc
    _ = (Fintype.card (Fin m) : ℝ)⁻¹ :=
      stdSimplex.barycenter_apply (𝕜 := ℝ) i
    _ = (m : ℝ)⁻¹ := by simp

/-- The Euclidean squared norm of the uniform weights is `1 / m`. -/
theorem norm_weightVector_barycenter_sq {m : ℕ} [NeZero m] :
    ‖weightVector (stdSimplex.barycenter : WeightSimplex m)‖ ^ 2 =
      1 / (m : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [weightVector, PiLp.toLp_apply]
  simp_rw [barycenter_weight_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  field_simp

/-- The uniform barycentric combination uses the row mean in its second block. -/
theorem barycentricMap_barycenter_eq {m : ℕ} [NeZero m] (W : RowMatrix m) :
    barycentricMap W (stdSimplex.barycenter : WeightSimplex m) =
      joinBlocks
        (a • weightVector (stdSimplex.barycenter : WeightSimplex m))
        (rowMean W) := by
  rw [barycentricMap_eq_joinBlocks]
  congr 1
  simp only [barycenter_weight_apply, rowMean]
  rw [Finset.smul_sum]

/-- Quantitative upper bound on the squared norm of the minimum point. -/
theorem norm_minPoint_sq_le {m : ℕ} [NeZero m] (W : RowMatrix m)
    (hW : Admissible W) :
    ‖minPoint W‖ ^ 2 ≤ a ^ 2 / (m : ℝ) + (tau m) ^ 2 := by
  have hmin := norm_minPoint_le W (stdSimplex.barycenter : WeightSimplex m)
  have hsquare : ‖minPoint W‖ ^ 2 ≤
      ‖barycentricMap W (stdSimplex.barycenter : WeightSimplex m)‖ ^ 2 := by
    nlinarith [norm_nonneg (minPoint W),
      norm_nonneg (barycentricMap W (stdSimplex.barycenter : WeightSimplex m))]
  calc
    ‖minPoint W‖ ^ 2 ≤
        ‖barycentricMap W (stdSimplex.barycenter : WeightSimplex m)‖ ^ 2 := hsquare
    _ = a ^ 2 / (m : ℝ) + ‖rowMean W‖ ^ 2 := by
      rw [barycentricMap_barycenter_eq, joinBlocks_norm_sq, norm_smul,
        Real.norm_eq_abs, abs_of_pos a_pos, mul_pow,
        norm_weightVector_barycenter_sq]
      ring
    _ ≤ a ^ 2 / (m : ℝ) + (tau m) ^ 2 := by
      gcongr
      exact norm_rowMean_le_tau W hW

/-- A convenient loose upper norm bound. -/
theorem norm_minPoint_le_two_a_div_sqrt {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    ‖minPoint W‖ ≤ 2 * a / Real.sqrt (m : ℝ) := by
  have hmnat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmnat
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  have hbound : a ^ 2 / (m : ℝ) + (tau m) ^ 2 ≤
      (2 * a / Real.sqrt (m : ℝ)) ^ 2 := by
    rw [tau, Gamma, a]
    field_simp
    nlinarith
  have hrhs : 0 ≤ 2 * a / Real.sqrt (m : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) a_pos.le) hs.le
  nlinarith [norm_minPoint_sq_le W hW |>.trans hbound, norm_nonneg (minPoint W)]

/-- The minimum point has strictly positive norm. -/
theorem norm_minPoint_pos {m : ℕ} [NeZero m] (W : RowMatrix m) :
    0 < ‖minPoint W‖ :=
  norm_pos_iff.mpr (minPoint_ne_zero W)

/-- The optimizer associated with the minimum-norm slope combination. -/
def hardOptimizer {m : ℕ} [NeZero m] (W : RowMatrix m) : QuerySpace m :=
  (-(‖minPoint W‖)⁻¹) • minPoint W

/-- The optimizer lies on the unit sphere. -/
@[simp]
theorem norm_hardOptimizer {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ‖hardOptimizer W‖ = 1 := by
  rw [hardOptimizer, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (minPoint_ne_zero W))

/-- Hence the optimizer belongs to the closed unit ball. -/
theorem hardOptimizer_mem_unitBall {m : ℕ} [NeZero m] (W : RowMatrix m) :
    hardOptimizer W ∈ unitBall m := by
  rw [mem_unitBall_iff, norm_hardOptimizer]

/-- Recover the minimum point from its normalized optimizer. -/
theorem minPoint_eq_neg_norm_smul_hardOptimizer {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    minPoint W = (-‖minPoint W‖) • hardOptimizer W := by
  rw [hardOptimizer, smul_smul]
  have hn : ‖minPoint W‖ ≠ 0 := norm_ne_zero_iff.mpr (minPoint_ne_zero W)
  rw [neg_mul_neg, mul_inv_cancel₀ hn, one_smul]

/-- The supporting functional takes value `-‖p‖` at the optimizer. -/
theorem inner_minPoint_hardOptimizer {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    inner ℝ (minPoint W) (hardOptimizer W) = -‖minPoint W‖ := by
  rw [hardOptimizer, inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖minPoint W‖ ≠ 0 := norm_ne_zero_iff.mpr (minPoint_ne_zero W)
  field_simp

/-- A simplex vertex maps to the corresponding hard slope. -/
@[simp]
theorem barycentricMap_vertex {m : ℕ} [NeZero m] (W : RowMatrix m) (i : Fin m) :
    barycentricMap W (stdSimplex.vertex i : WeightSimplex m) = slope W i := by
  rw [barycentricMap_apply]
  simp [stdSimplex.vertex]

/-- Projection against a vertex gives the basic slope inequality. -/
theorem norm_minPoint_sq_le_inner_slope {m : ℕ} [NeZero m]
    (W : RowMatrix m) (i : Fin m) :
    ‖minPoint W‖ ^ 2 ≤ inner ℝ (minPoint W) (slope W i) := by
  have hproj := minPoint_projection W (stdSimplex.vertex i : WeightSimplex m)
  rw [barycentricMap_vertex, inner_sub_right, real_inner_self_eq_norm_sq] at hproj
  linarith

/-- Every row value at the optimizer is at most `-‖p‖`. -/
theorem rowValue_hardOptimizer_le {m : ℕ} [NeZero m]
    (W : RowMatrix m) (i : Fin m) :
    rowValue W i (hardOptimizer W) ≤ -‖minPoint W‖ := by
  have hslope := norm_minPoint_sq_le_inner_slope W i
  have hcoeff : -(‖minPoint W‖)⁻¹ ≤ 0 := by
    exact neg_nonpos.mpr (inv_nonneg.mpr (norm_nonneg _))
  calc
    rowValue W i (hardOptimizer W) =
        (-(‖minPoint W‖)⁻¹) * inner ℝ (minPoint W) (slope W i) := by
      rw [rowValue, hardOptimizer, inner_smul_right,
        real_inner_comm (slope W i) (minPoint W)]
    _ ≤ (-(‖minPoint W‖)⁻¹) * ‖minPoint W‖ ^ 2 :=
      mul_le_mul_of_nonpos_left hslope hcoeff
    _ = -‖minPoint W‖ := by
      have hn : ‖minPoint W‖ ≠ 0 := norm_ne_zero_iff.mpr (minPoint_ne_zero W)
      field_simp

/-- The minimum point supplies a global affine lower support for the hard objective. -/
theorem inner_minPoint_le_hardObjective {m : ℕ} [NeZero m]
    (W : RowMatrix m) (q : QuerySpace m) :
    inner ℝ (minPoint W) q ≤ hardObjective W q := by
  calc
    inner ℝ (minPoint W) q =
        ∑ i, (minWeights W : Fin m → ℝ) i * rowValue W i q := by
      rw [minPoint, barycentricMap_apply, sum_inner]
      simp only [real_inner_smul_left, rowValue]
    _ ≤ ∑ i, (minWeights W : Fin m → ℝ) i * hardObjective W q := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (rowValue_le_hardObjective W i q)
        ((minWeights W).2.1 i)
    _ = hardObjective W q := by
      change (∑ i, (minWeights W).val i * hardObjective W q) =
        hardObjective W q
      rw [← Finset.sum_mul, (minWeights W).property.2, one_mul]

/-- Exact value of the hard objective at its optimizer. -/
@[simp]
theorem hardObjective_hardOptimizer {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    hardObjective W (hardOptimizer W) = -‖minPoint W‖ := by
  apply le_antisymm
  · exact hardObjective_le W (hardOptimizer W) fun i ↦ rowValue_hardOptimizer_le W i
  · rw [← inner_minPoint_hardOptimizer W]
    exact inner_minPoint_le_hardObjective W (hardOptimizer W)

/-- The value `-‖p‖` is a lower bound throughout the unit ball. -/
theorem neg_norm_minPoint_le_hardObjective {m : ℕ} [NeZero m]
    (W : RowMatrix m) {q : QuerySpace m} (hq : q ∈ unitBall m) :
    -‖minPoint W‖ ≤ hardObjective W q := by
  have hqnorm : ‖q‖ ≤ 1 := mem_unitBall_iff.mp hq
  have hinner : -‖minPoint W‖ * ‖q‖ ≤ inner ℝ (minPoint W) q := by
    simpa only [neg_mul] using
      neg_le_of_abs_le (abs_real_inner_le_norm (minPoint W) q)
  calc
    -‖minPoint W‖ ≤ -‖minPoint W‖ * ‖q‖ := by
      nlinarith [norm_nonneg (minPoint W), norm_nonneg q]
    _ ≤ inner ℝ (minPoint W) q := hinner
    _ ≤ hardObjective W q := inner_minPoint_le_hardObjective W q

/-- The normalized minimum point minimizes the hard objective on the unit ball. -/
theorem hardOptimizer_isMinOn {m : ℕ} [NeZero m] (W : RowMatrix m) :
    IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) := by
  intro q hq
  rw [hardObjective_hardOptimizer]
  exact neg_norm_minPoint_le_hardObjective W hq

/-- Quadratic objective growth away from the optimizer, equation (7.7). -/
theorem hardObjective_growth {m : ℕ} [NeZero m] (W : RowMatrix m)
    {q : QuerySpace m} (hq : q ∈ unitBall m) :
    ‖minPoint W‖ / 2 * ‖q - hardOptimizer W‖ ^ 2 ≤
      hardObjective W q - hardObjective W (hardOptimizer W) := by
  have hqnorm : ‖q‖ ≤ 1 := mem_unitBall_iff.mp hq
  have hqnormsq : ‖q‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg q]
  have hdist_formula := norm_sub_sq_real q (hardOptimizer W)
  have hgeom : ‖q - hardOptimizer W‖ ^ 2 ≤
      2 * (1 - inner ℝ q (hardOptimizer W)) := by
    rw [norm_hardOptimizer] at hdist_formula
    nlinarith
  have hgeom_half : ‖q - hardOptimizer W‖ ^ 2 / 2 ≤
      1 - inner ℝ q (hardOptimizer W) := by
    linarith
  have hinner_formula : inner ℝ (minPoint W) q =
      -‖minPoint W‖ * inner ℝ (hardOptimizer W) q := by
    calc
      inner ℝ (minPoint W) q =
          inner ℝ ((-‖minPoint W‖) • hardOptimizer W) q :=
        congrArg (fun x : QuerySpace m ↦ inner ℝ x q)
          (minPoint_eq_neg_norm_smul_hardOptimizer W)
      _ = -‖minPoint W‖ * inner ℝ (hardOptimizer W) q := by
        rw [real_inner_smul_left]
  calc
    ‖minPoint W‖ / 2 * ‖q - hardOptimizer W‖ ^ 2 =
        ‖minPoint W‖ * (‖q - hardOptimizer W‖ ^ 2 / 2) := by ring
    _ ≤ ‖minPoint W‖ * (1 - inner ℝ q (hardOptimizer W)) :=
      mul_le_mul_of_nonneg_left hgeom_half (norm_nonneg _)
    _ = inner ℝ (minPoint W) q + ‖minPoint W‖ := by
      rw [hinner_formula, real_inner_comm q (hardOptimizer W)]
      ring
    _ ≤ hardObjective W q + ‖minPoint W‖ :=
      add_le_add_left (inner_minPoint_le_hardObjective W q) _
    _ = hardObjective W q - hardObjective W (hardOptimizer W) := by
      rw [hardObjective_hardOptimizer]
      ring

/-- The optimizer is the unique point attaining the minimum value on the unit ball. -/
theorem hardOptimizer_unique {m : ℕ} [NeZero m] (W : RowMatrix m)
    {q : QuerySpace m} (hq : q ∈ unitBall m)
    (hqval : hardObjective W q = -‖minPoint W‖) :
    q = hardOptimizer W := by
  have hgrowth := hardObjective_growth W hq
  rw [hqval, hardObjective_hardOptimizer] at hgrowth
  have hnormpos := norm_minPoint_pos W
  have hgrowth_zero :
      ‖minPoint W‖ / 2 * ‖q - hardOptimizer W‖ ^ 2 ≤ 0 := by
    linarith
  have hsquare_nonpos : ‖q - hardOptimizer W‖ ^ 2 ≤ 0 := by
    by_contra h
    have hsquare_pos : 0 < ‖q - hardOptimizer W‖ ^ 2 := lt_of_not_ge h
    have hproduct_pos :
        0 < ‖minPoint W‖ / 2 * ‖q - hardOptimizer W‖ ^ 2 :=
      mul_pos (div_pos hnormpos (by norm_num)) hsquare_pos
    exact (not_lt_of_ge hgrowth_zero) hproduct_pos
  have hdist : ‖q - hardOptimizer W‖ = 0 := by
    exact sq_eq_zero_iff.mp
      (le_antisymm hsquare_nonpos (sq_nonneg ‖q - hardOptimizer W‖))
  exact sub_eq_zero.mp (norm_eq_zero.mp hdist)

/-- Uniqueness in the usual `IsMinOn` formulation. -/
theorem hardOptimizer_eq_of_isMinOn {m : ℕ} [NeZero m] (W : RowMatrix m)
    {q : QuerySpace m} (hq : q ∈ unitBall m)
    (hmin : IsMinOn (hardObjective W) (unitBall m) q) :
    q = hardOptimizer W := by
  apply hardOptimizer_unique W hq
  apply le_antisymm
  · simpa using hmin (hardOptimizer_mem_unitBall W)
  · exact neg_norm_minPoint_le_hardObjective W hq

end ZeroOrderBounds
