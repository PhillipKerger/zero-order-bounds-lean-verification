import FullDMinusOneHalfAccuracy.Statement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Passing the even-dimensional lower bound to an odd dimension

This file formalizes the reduction used at the start of the paper.  An exact-value
algorithm in dimension `2m + 1` is simulated in dimension `2m`: each query and the
final output are orthogonally projected onto the first `2m` coordinates, arranged
as the two blocks of `QuerySpace m`.  Conversely, an even-dimensional hard objective
is lifted by making it independent of the remaining coordinate.

The reduction is deliberately stated for arbitrary deterministic strategies and
arbitrary functions before it is specialized to the max-affine hard family.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-! ## Dimension-independent exact-value strategies -/

/-- The standard `d`-dimensional Euclidean query space. -/
abbrev AmbientQuerySpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The closed unit ball in the standard `d`-dimensional Euclidean space. -/
def ambientUnitBall (d : ℕ) : Set (AmbientQuerySpace d) :=
  closedBall 0 1

@[simp]
theorem mem_ambientUnitBall_iff {d : ℕ} {q : AmbientQuerySpace d} :
    q ∈ ambientUnitBall d ↔ ‖q‖ ≤ 1 := by
  simp [ambientUnitBall]

/-- A point of the standard Euclidean unit ball. -/
abbrev AmbientUnitBall (d : ℕ) :=
  {q : AmbientQuerySpace d // q ∈ ambientUnitBall d}

/-- An arbitrary deterministic exact-value strategy in dimension `d`. -/
structure AmbientDeterministicStrategy (d : ℕ) where
  query : List ℝ → AmbientUnitBall d
  output : List ℝ → AmbientUnitBall d

namespace AmbientDeterministicStrategy

variable {d : ℕ}

/-- The query generated from the first `t` entries of a proposed transcript. -/
def queryAt (A : AmbientDeterministicStrategy d) (ys : List ℝ) (t : ℕ) :
    AmbientUnitBall d :=
  A.query (ys.take t)

@[simp]
theorem queryAt_length (A : AmbientDeterministicStrategy d) (ys : List ℝ) :
    A.queryAt ys ys.length = A.query ys := by
  simp [queryAt]

@[simp]
theorem query_mem_unitBall (A : AmbientDeterministicStrategy d) (ys : List ℝ) :
    (A.query ys : AmbientQuerySpace d) ∈ ambientUnitBall d :=
  (A.query ys).property

@[simp]
theorem output_mem_unitBall (A : AmbientDeterministicStrategy d) (ys : List ℝ) :
    (A.output ys : AmbientQuerySpace d) ∈ ambientUnitBall d :=
  (A.output ys).property

end AmbientDeterministicStrategy

/-- Exact transcript consistency for a general objective in a standard Euclidean
space. -/
def AmbientConsistent {d : ℕ} (A : AmbientDeterministicStrategy d)
    (ys : List ℝ) (f : AmbientQuerySpace d → ℝ) : Prop :=
  ∀ (t : ℕ) (ht : t < ys.length),
    f (A.queryAt ys t : AmbientQuerySpace d) = ys[t]

/-! ## The orthogonal splitting `ℝ^(2m+1) = QuerySpace m ⊕ ℝ` -/

/-- Reindex the standard coordinates in dimension `2m+1` into the two `m`-blocks
used by the hard family, followed by one remaining coordinate. -/
def oddIndexEquiv (m : ℕ) :
    Fin (2 * m + 1) ≃ (Fin m ⊕ Fin m) ⊕ Fin 1 :=
  (finCongr (by omega : 2 * m + 1 = (m + m) + 1)).trans <|
    (@finSumFinEquiv (m + m) 1).symm.trans <|
      Equiv.sumCongr (@finSumFinEquiv m m).symm (Equiv.refl (Fin 1))

/-- The coordinate of the first block inside the standard odd-dimensional
coordinate ordering. -/
def oddFirstIndex (m : ℕ) (i : Fin m) : Fin (2 * m + 1) :=
  ⟨i, by omega⟩

/-- The coordinate of the second block inside the standard odd-dimensional
coordinate ordering. -/
def oddSecondIndex (m : ℕ) (i : Fin m) : Fin (2 * m + 1) :=
  ⟨m + i, by omega⟩

/-- The single coordinate omitted by `oddProject`. -/
def oddLastIndex (m : ℕ) : Fin (2 * m + 1) :=
  Fin.last (2 * m)

@[simp]
theorem oddIndexEquiv_symm_first (m : ℕ) (i : Fin m) :
    (oddIndexEquiv m).symm (Sum.inl (Sum.inl i)) = oddFirstIndex m i := by
  ext
  simp [oddIndexEquiv, oddFirstIndex]

@[simp]
theorem oddIndexEquiv_symm_second (m : ℕ) (i : Fin m) :
    (oddIndexEquiv m).symm (Sum.inl (Sum.inr i)) = oddSecondIndex m i := by
  ext
  simp [oddIndexEquiv, oddSecondIndex]
  omega

@[simp]
theorem oddIndexEquiv_symm_last (m : ℕ) :
    (oddIndexEquiv m).symm (Sum.inr (0 : Fin 1)) = oddLastIndex m := by
  ext
  simp [oddIndexEquiv, oddLastIndex]

/-- The canonical orthogonal coordinate splitting of odd-dimensional space. -/
def oddSplit (m : ℕ) :
    AmbientQuerySpace (2 * m + 1) ≃ₗᵢ[ℝ]
      WithLp 2 (QuerySpace m × EuclideanSpace ℝ (Fin 1)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (oddIndexEquiv m)).trans <|
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)

/-- Orthogonal projection from dimension `2m+1` to the first `2m` coordinates. -/
def oddProject {m : ℕ} (q : AmbientQuerySpace (2 * m + 1)) : QuerySpace m :=
  (WithLp.ofLp (oddSplit m q)).1

/-- `oddProject` really selects standard coordinates `0,...,m-1` for its first
block. -/
@[simp]
theorem oddProject_apply_first {m : ℕ}
    (q : AmbientQuerySpace (2 * m + 1)) (i : Fin m) :
    oddProject q (Sum.inl i) = q (oddFirstIndex m i) := by
  simp [oddProject, oddSplit]

/-- Its second block consists of standard coordinates `m,...,2m-1`. -/
@[simp]
theorem oddProject_apply_second {m : ℕ}
    (q : AmbientQuerySpace (2 * m + 1)) (i : Fin m) :
    oddProject q (Sum.inr i) = q (oddSecondIndex m i) := by
  simp [oddProject, oddSplit]

/-- Join an even-dimensional vector and a remaining one-dimensional coordinate. -/
def oddJoin {m : ℕ} (q : QuerySpace m) (z : EuclideanSpace ℝ (Fin 1)) :
    AmbientQuerySpace (2 * m + 1) :=
  (oddSplit m).symm (WithLp.toLp 2 (q, z))

/-- Include the first `2m` coordinates into dimension `2m+1`, setting the last
coordinate to zero. -/
def oddEmbed {m : ℕ} (q : QuerySpace m) : AmbientQuerySpace (2 * m + 1) :=
  oddJoin q 0

@[simp]
theorem oddProject_oddJoin {m : ℕ} (q : QuerySpace m)
    (z : EuclideanSpace ℝ (Fin 1)) :
    oddProject (oddJoin q z) = q := by
  simp [oddProject, oddJoin]

@[simp]
theorem oddProject_oddEmbed {m : ℕ} (q : QuerySpace m) :
    oddProject (oddEmbed q) = q := by
  simp [oddEmbed]

@[simp]
theorem norm_oddEmbed {m : ℕ} (q : QuerySpace m) :
    ‖oddEmbed q‖ = ‖q‖ := by
  rw [oddEmbed, oddJoin, (oddSplit m).symm.norm_map]
  simp

/-- Orthogonal projection does not increase the Euclidean norm. -/
theorem norm_oddProject_le {m : ℕ} (q : AmbientQuerySpace (2 * m + 1)) :
    ‖oddProject q‖ ≤ ‖q‖ := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (oddSplit m q)
  have hnorm : ‖oddSplit m q‖ = ‖q‖ := (oddSplit m).norm_map q
  rw [← hnorm]
  dsimp [oddProject]
  nlinarith [sq_nonneg ‖(WithLp.ofLp (oddSplit m q)).2‖,
    norm_nonneg ((WithLp.ofLp (oddSplit m q)).1),
    norm_nonneg (oddSplit m q)]

@[simp]
theorem oddProject_zero {m : ℕ} :
    oddProject (0 : AmbientQuerySpace (2 * m + 1)) = 0 := by
  simp [oddProject]

@[simp]
theorem oddProject_add {m : ℕ}
    (q r : AmbientQuerySpace (2 * m + 1)) :
    oddProject (q + r) = oddProject q + oddProject r := by
  simp [oddProject]

@[simp]
theorem oddProject_smul {m : ℕ} (c : ℝ)
    (q : AmbientQuerySpace (2 * m + 1)) :
    oddProject (c • q) = c • oddProject q := by
  simp [oddProject]

@[simp]
theorem oddProject_sub {m : ℕ}
    (q r : AmbientQuerySpace (2 * m + 1)) :
    oddProject (q - r) = oddProject q - oddProject r := by
  rw [sub_eq_add_neg, oddProject_add, sub_eq_add_neg]
  congr 1

/-- `oddProject` bundled as a linear map, for transporting convexity. -/
def oddProjectLinearMap (m : ℕ) :
    AmbientQuerySpace (2 * m + 1) →ₗ[ℝ] QuerySpace m where
  toFun := oddProject
  map_add' := oddProject_add
  map_smul' := oddProject_smul

@[simp]
theorem oddProjectLinearMap_apply {m : ℕ}
    (q : AmbientQuerySpace (2 * m + 1)) :
    oddProjectLinearMap m q = oddProject q :=
  rfl

/-- The orthogonal projection is one-Lipschitz. -/
theorem oddProject_lipschitzWith_one {m : ℕ} :
    LipschitzWith 1 (@oddProject m) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  simpa [dist_eq_norm] using norm_oddProject_le (q - r)

/-! ## Projecting strategies and lifting objectives -/

/-- Simulate an odd-dimensional strategy in the even-dimensional block space by
projecting each query and the output. -/
def projectOddStrategy {m : ℕ}
    (A : AmbientDeterministicStrategy (2 * m + 1)) :
    DeterministicStrategy m where
  query ys :=
    ⟨oddProject (A.query ys : AmbientQuerySpace (2 * m + 1)), by
      rw [mem_unitBall_iff]
      exact (norm_oddProject_le _).trans
        (mem_ambientUnitBall_iff.mp (A.query_mem_unitBall ys))⟩
  output ys :=
    ⟨oddProject (A.output ys : AmbientQuerySpace (2 * m + 1)), by
      rw [mem_unitBall_iff]
      exact (norm_oddProject_le _).trans
        (mem_ambientUnitBall_iff.mp (A.output_mem_unitBall ys))⟩

@[simp]
theorem projectOddStrategy_query {m : ℕ}
    (A : AmbientDeterministicStrategy (2 * m + 1)) (ys : List ℝ) :
    ((projectOddStrategy A).query ys : QuerySpace m) =
      oddProject (A.query ys : AmbientQuerySpace (2 * m + 1)) :=
  rfl

@[simp]
theorem projectOddStrategy_output {m : ℕ}
    (A : AmbientDeterministicStrategy (2 * m + 1)) (ys : List ℝ) :
    ((projectOddStrategy A).output ys : QuerySpace m) =
      oddProject (A.output ys : AmbientQuerySpace (2 * m + 1)) :=
  rfl

@[simp]
theorem projectOddStrategy_queryAt {m : ℕ}
    (A : AmbientDeterministicStrategy (2 * m + 1)) (ys : List ℝ) (t : ℕ) :
    ((projectOddStrategy A).queryAt ys t : QuerySpace m) =
      oddProject (A.queryAt ys t : AmbientQuerySpace (2 * m + 1)) :=
  rfl

/-- Lift an even-dimensional objective by making it independent of the final
coordinate. -/
def oddLiftObjective {m : ℕ} (f : QuerySpace m → ℝ) :
    AmbientQuerySpace (2 * m + 1) → ℝ :=
  fun q ↦ f (oddProject q)

@[simp]
theorem oddLiftObjective_oddJoin {m : ℕ} (f : QuerySpace m → ℝ)
    (q : QuerySpace m) (z : EuclideanSpace ℝ (Fin 1)) :
    oddLiftObjective f (oddJoin q z) = f q := by
  simp [oddLiftObjective]

@[simp]
theorem oddLiftObjective_oddEmbed {m : ℕ} (f : QuerySpace m → ℝ)
    (q : QuerySpace m) :
    oddLiftObjective f (oddEmbed q) = f q := by
  simp [oddLiftObjective]

/-- The lifted objective is constant on every fiber of the projection. -/
theorem oddLiftObjective_eq_of_project_eq {m : ℕ} (f : QuerySpace m → ℝ)
    {q r : AmbientQuerySpace (2 * m + 1)}
    (hqr : oddProject q = oddProject r) :
    oddLiftObjective f q = oddLiftObjective f r := by
  simp [oddLiftObjective, hqr]

@[simp]
theorem oddLiftObjective_zero {m : ℕ} (f : QuerySpace m → ℝ) :
    oddLiftObjective f 0 = f 0 := by
  simp [oddLiftObjective]

/-- Convexity is preserved by the coordinate lift. -/
theorem convexOn_oddLiftObjective {m : ℕ} {f : QuerySpace m → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (oddLiftObjective f) := by
  refine ⟨convex_univ, ?_⟩
  intro q _ r _ a b ha hb hab
  change f (oddProject (a • q + b • r)) ≤
    a • f (oddProject q) + b • f (oddProject r)
  rw [oddProject_add, oddProject_smul, oddProject_smul]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-- A one-Lipschitz objective remains one-Lipschitz after the coordinate lift. -/
theorem oddLiftObjective_lipschitzWith_one {m : ℕ} {f : QuerySpace m → ℝ}
    (hf : LipschitzWith 1 f) :
    LipschitzWith 1 (oddLiftObjective f) := by
  change LipschitzWith 1 (fun q ↦ f (oddProject q))
  apply LipschitzWith.mk_one
  intro q r
  calc
    dist (f (oddProject q)) (f (oddProject r)) ≤
        dist (oddProject q) (oddProject r) := by
      simpa only [NNReal.coe_one, one_mul] using
        hf.dist_le_mul (oddProject q) (oddProject r)
    _ ≤ dist q r := by
      simpa [dist_eq_norm] using norm_oddProject_le (q - r)

/-- Embedding an even-dimensional unit-ball point produces an odd-dimensional
unit-ball point. -/
theorem oddEmbed_mem_ambientUnitBall {m : ℕ} {q : QuerySpace m}
    (hq : q ∈ unitBall m) :
    oddEmbed q ∈ ambientUnitBall (2 * m + 1) := by
  rw [mem_ambientUnitBall_iff, norm_oddEmbed]
  exact mem_unitBall_iff.mp hq

/-- A unit-ball minimizer stays a minimizer after lifting the objective. -/
theorem oddLiftObjective_isMinOn {m : ℕ} {f : QuerySpace m → ℝ}
    {q : QuerySpace m} (hmin : IsMinOn f (unitBall m) q) :
    IsMinOn (oddLiftObjective f) (ambientUnitBall (2 * m + 1)) (oddEmbed q) := by
  intro r hr
  rw [oddLiftObjective_oddEmbed]
  apply hmin
  rw [mem_unitBall_iff]
  exact (norm_oddProject_le r).trans (mem_ambientUnitBall_iff.mp hr)

/-! ## Specialization to the hard max-affine family -/

/-- The paper's hard max-affine objective in dimension `2m`, lifted to dimension
`2m+1` by ignoring the final coordinate. -/
def oddHardObjective {m : ℕ} [NeZero m] (W : RowMatrix m) :
    AmbientQuerySpace (2 * m + 1) → ℝ :=
  oddLiftObjective (hardObjective W)

/-- The canonical hard optimizer embedded with last coordinate zero. -/
def oddHardOptimizer {m : ℕ} [NeZero m] (W : RowMatrix m) :
    AmbientQuerySpace (2 * m + 1) :=
  oddEmbed (hardOptimizer W)

@[simp]
theorem oddHardObjective_apply {m : ℕ} [NeZero m] (W : RowMatrix m)
    (q : AmbientQuerySpace (2 * m + 1)) :
    oddHardObjective W q = hardObjective W (oddProject q) :=
  rfl

@[simp]
theorem oddHardObjective_oddJoin {m : ℕ} [NeZero m] (W : RowMatrix m)
    (q : QuerySpace m) (z : EuclideanSpace ℝ (Fin 1)) :
    oddHardObjective W (oddJoin q z) = hardObjective W q := by
  simp [oddHardObjective]

@[simp]
theorem oddHardObjective_oddEmbed {m : ℕ} [NeZero m] (W : RowMatrix m)
    (q : QuerySpace m) :
    oddHardObjective W (oddEmbed q) = hardObjective W q := by
  simp [oddHardObjective]

@[simp]
theorem oddHardObjective_oddHardOptimizer {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    oddHardObjective W (oddHardOptimizer W) =
      hardObjective W (hardOptimizer W) := by
  simp [oddHardOptimizer]

@[simp]
theorem oddHardObjective_zero {m : ℕ} [NeZero m] (W : RowMatrix m) :
    oddHardObjective W 0 = 0 := by
  simp [oddHardObjective]

theorem convexOn_oddHardObjective {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    ConvexOn ℝ Set.univ (oddHardObjective W) :=
  convexOn_oddLiftObjective (convexOn_hardObjective W)

theorem oddHardObjective_lipschitzWith_one {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    LipschitzWith 1 (oddHardObjective W) :=
  oddLiftObjective_lipschitzWith_one
    (hardObjective_lipschitzWith_one W hW)

theorem oddHardOptimizer_mem_ambientUnitBall {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    oddHardOptimizer W ∈ ambientUnitBall (2 * m + 1) := by
  apply oddEmbed_mem_ambientUnitBall
  exact hardOptimizer_mem_unitBall W

theorem oddHardOptimizer_isMinOn {m : ℕ} [NeZero m]
    (W : RowMatrix m) :
    IsMinOn (oddHardObjective W) (ambientUnitBall (2 * m + 1))
      (oddHardOptimizer W) := by
  exact oddLiftObjective_isMinOn (hardOptimizer_isMinOn W)

/-- Exact hard-family consistency is preserved by the projected simulation. -/
theorem ambientConsistent_oddHardObjective_iff {m : ℕ} [NeZero m]
    (A : AmbientDeterministicStrategy (2 * m + 1))
    (ys : List ℝ) (W : RowMatrix m) :
    AmbientConsistent A ys (oddHardObjective W) ↔
      Consistent (projectOddStrategy A) ys W := by
  rfl

/-- One direction of transcript transport, convenient at the lower-bound
endpoint. -/
theorem AmbientConsistent.of_projectOddStrategy {m : ℕ} [NeZero m]
    {A : AmbientDeterministicStrategy (2 * m + 1)}
    {ys : List ℝ} {W : RowMatrix m}
    (h : Consistent (projectOddStrategy A) ys W) :
    AmbientConsistent A ys (oddHardObjective W) :=
  (ambientConsistent_oddHardObjective_iff A ys W).2 h

/-- The output error is unchanged by projection and coordinate lifting. -/
theorem oddHardObjective_gap_eq {m : ℕ} [NeZero m]
    (A : AmbientDeterministicStrategy (2 * m + 1))
    (ys : List ℝ) (W : RowMatrix m) :
    oddHardObjective W
          (A.output ys : AmbientQuerySpace (2 * m + 1)) -
        oddHardObjective W (oddHardOptimizer W) =
      hardObjective W
          ((projectOddStrategy A).output ys : QuerySpace m) -
        hardObjective W (hardOptimizer W) := by
  rw [oddHardObjective_apply, oddHardObjective_oddHardOptimizer,
    projectOddStrategy_output]

/-! ## The odd-dimensional fixed-horizon endpoint -/

/-- The paper's numerical accuracy written directly as a function of the ambient
dimension. -/
def ambientSqrtAccuracy (d : ℕ) : ℝ :=
  1 / (10000000 * Real.sqrt (d : ℝ))

/-- The target accuracy in ambient dimension `2m+1`. -/
def oddSqrtAccuracy (m : ℕ) : ℝ :=
  ambientSqrtAccuracy (2 * m + 1)

@[simp]
theorem ambientSqrtAccuracy_even (m : ℕ) :
    ambientSqrtAccuracy (2 * m) = sqrtAccuracy m := by
  simp [ambientSqrtAccuracy, sqrtAccuracy, Nat.cast_mul]

/-- Increasing the ambient dimension from `2m` to `2m+1` weakens the target
accuracy. -/
theorem oddSqrtAccuracy_le_sqrtAccuracy (m : ℕ) [NeZero m] :
    oddSqrtAccuracy m ≤ sqrtAccuracy m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hradicand : 2 * (m : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    norm_num
  have hsqrt : Real.sqrt (2 * (m : ℝ)) ≤
      Real.sqrt (((2 * m + 1 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hradicand
  have hdenom : 10000000 * Real.sqrt (2 * (m : ℝ)) ≤
      10000000 * Real.sqrt (((2 * m + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hdenom_pos :
      0 < 10000000 * Real.sqrt (2 * (m : ℝ)) := by
    positivity
  exact one_div_le_one_div_of_le hdenom_pos hdenom

/-- The complete even-dimensional conclusion packaged so that the geometric
proof and this dimension reduction have a narrow interface. -/
def EvenFixedHorizonConclusion (m T : ℕ) [NeZero m]
    (A : DeterministicStrategy m) : Prop :=
  ∃ ys : List ℝ, ∃ W : RowMatrix m,
    ys.length = T ∧
    Admissible W ∧
    hardObjective W 0 = 0 ∧
    ConvexOn ℝ Set.univ (hardObjective W) ∧
    LipschitzWith 1 (hardObjective W) ∧
    Consistent A ys W ∧
    hardOptimizer W ∈ unitBall m ∧
    IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) ∧
    sqrtAccuracy m <
      hardObjective W (A.output ys : QuerySpace m) -
        hardObjective W (hardOptimizer W)

/-- The corresponding conclusion for the lifted objective in dimension
`2m+1`. -/
def OddFixedHorizonConclusion (m T : ℕ) [NeZero m]
    (A : AmbientDeterministicStrategy (2 * m + 1)) : Prop :=
  ∃ ys : List ℝ, ∃ W : RowMatrix m,
    ys.length = T ∧
    Admissible W ∧
    oddHardObjective W 0 = 0 ∧
    ConvexOn ℝ Set.univ (oddHardObjective W) ∧
    LipschitzWith 1 (oddHardObjective W) ∧
    AmbientConsistent A ys (oddHardObjective W) ∧
    oddHardOptimizer W ∈ ambientUnitBall (2 * m + 1) ∧
    IsMinOn (oddHardObjective W) (ambientUnitBall (2 * m + 1))
      (oddHardOptimizer W) ∧
    oddSqrtAccuracy m <
      oddHardObjective W
          (A.output ys : AmbientQuerySpace (2 * m + 1)) -
        oddHardObjective W (oddHardOptimizer W)

/-- The exact odd-dimensional reduction: a lower-bound witness for the projected
even-dimensional simulation gives a witness for the original algorithm. -/
theorem oddFixedHorizonConclusion_of_even {m T : ℕ} [NeZero m]
    (A : AmbientDeterministicStrategy (2 * m + 1))
    (hEven : EvenFixedHorizonConclusion m T (projectOddStrategy A)) :
    OddFixedHorizonConclusion m T A := by
  obtain ⟨ys, W, hlen, hW, _hzero, _hconvex, _hlipschitz,
    hconsistent, _hoptimizer, _hmin, hgap⟩ := hEven
  refine ⟨ys, W, hlen, hW, oddHardObjective_zero W,
    convexOn_oddHardObjective W, oddHardObjective_lipschitzWith_one W hW,
    AmbientConsistent.of_projectOddStrategy hconsistent,
    oddHardOptimizer_mem_ambientUnitBall W, oddHardOptimizer_isMinOn W, ?_⟩
  rw [oddHardObjective_gap_eq]
  exact (oddSqrtAccuracy_le_sqrtAccuracy m).trans_lt hgap

/-- A universal even-dimensional fixed-horizon endpoint therefore implies the
odd-dimensional endpoint for every deterministic exact-value algorithm. -/
theorem oddFixedHorizonLowerBound_strict_of_even {m T : ℕ} [NeZero m]
    (hEven : ∀ B : DeterministicStrategy m,
      EvenFixedHorizonConclusion m T B)
    (A : AmbientDeterministicStrategy (2 * m + 1)) :
    OddFixedHorizonConclusion m T A :=
  oddFixedHorizonConclusion_of_even A (hEven (projectOddStrategy A))

end ZeroOrderBounds.AccuracyImprovement
