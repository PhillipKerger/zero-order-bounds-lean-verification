import FullDMinusOneHalfAccuracy.Statement

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Scaling the unit-radius, unit-Lipschitz lower bound

The resisting-oracle construction is carried out on the unit ball for
one-Lipschitz objectives.  This file records the exact change of variables used
in the paper to obtain the statement on a ball of radius `R` for `L`-Lipschitz
objectives.  Both the query points and every oracle answer in a transcript are
rescaled; this matters because a deterministic strategy may inspect the exact
real answers before selecting its next query.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-! ## Points, transcripts, and strategies at radius `R` -/

/-- The closed Euclidean ball of radius `R` in the even-dimensional block
space. -/
def radiusBall (m : ℕ) (R : ℝ) : Set (QuerySpace m) :=
  closedBall 0 R

/-- A query bundled with its radius-`R` feasibility certificate. -/
abbrev RadiusBall (m : ℕ) (R : ℝ) :=
  {q : QuerySpace m // q ∈ radiusBall m R}

/-- A deterministic exact-value strategy whose queries and output lie in the
closed ball of radius `R`. -/
structure RadiusDeterministicStrategy (m : ℕ) (R : ℝ) where
  query : List ℝ → RadiusBall m R
  output : List ℝ → RadiusBall m R

namespace RadiusDeterministicStrategy

variable {m : ℕ} {R : ℝ}

/-- Query selected after the first `t` answers of a proposed transcript. -/
def queryAt (A : RadiusDeterministicStrategy m R) (ys : List ℝ) (t : ℕ) :
    RadiusBall m R :=
  A.query (ys.take t)

@[simp]
theorem queryAt_length (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    A.queryAt ys ys.length = A.query ys := by
  simp [queryAt]

@[simp]
theorem query_mem_radiusBall (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    (A.query ys : QuerySpace m) ∈ radiusBall m R :=
  (A.query ys).property

@[simp]
theorem output_mem_radiusBall (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    (A.output ys : QuerySpace m) ∈ radiusBall m R :=
  (A.output ys).property

end RadiusDeterministicStrategy

/-- Exact transcript consistency for a general objective on the radius-`R`
ball. -/
def RadiusConsistent {m : ℕ} {R : ℝ}
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ)
    (f : QuerySpace m → ℝ) : Prop :=
  ∀ (t : ℕ) (ht : t < ys.length),
    f (A.queryAt ys t : QuerySpace m) = ys[t]

/-- Multiply every exact oracle answer by the objective scale `c`. -/
def scaleAnswers (c : ℝ) (ys : List ℝ) : List ℝ :=
  ys.map fun y ↦ c * y

@[simp]
theorem length_scaleAnswers (c : ℝ) (ys : List ℝ) :
    (scaleAnswers c ys).length = ys.length := by
  simp [scaleAnswers]

@[simp]
theorem scaleAnswers_nil (c : ℝ) : scaleAnswers c [] = [] := rfl

@[simp]
theorem scaleAnswers_take (c : ℝ) (ys : List ℝ) (t : ℕ) :
    scaleAnswers c (ys.take t) = (scaleAnswers c ys).take t := by
  simp [scaleAnswers]

@[simp]
theorem scaleAnswers_one (ys : List ℝ) : scaleAnswers 1 ys = ys := by
  simp [scaleAnswers]

theorem scaleAnswers_scaleAnswers (c d : ℝ) (ys : List ℝ) :
    scaleAnswers c (scaleAnswers d ys) = scaleAnswers (c * d) ys := by
  simp [scaleAnswers, List.map_map, Function.comp_def, mul_assoc]

@[simp]
theorem scaleAnswers_inv_scaleAnswers {c : ℝ} (hc : c ≠ 0) (ys : List ℝ) :
    scaleAnswers c⁻¹ (scaleAnswers c ys) = ys := by
  rw [scaleAnswers_scaleAnswers, inv_mul_cancel₀ hc, scaleAnswers_one]

@[simp]
theorem scaleAnswers_scaleAnswers_inv {c : ℝ} (hc : c ≠ 0) (ys : List ℝ) :
    scaleAnswers c (scaleAnswers c⁻¹ ys) = ys := by
  rw [scaleAnswers_scaleAnswers, mul_inv_cancel₀ hc, scaleAnswers_one]

@[simp]
theorem getElem_scaleAnswers (c : ℝ) (ys : List ℝ) (t : ℕ)
    (ht : t < ys.length) :
    (scaleAnswers c ys)[t]'(by simpa using ht) = c * ys[t]'ht := by
  simp [scaleAnswers]

/-- Scaling a point from the unit model to radius `R`. -/
def scalePoint (R : ℝ) {m : ℕ} (q : QuerySpace m) : QuerySpace m :=
  R • q

/-- Scaling a radius-`R` point back to the unit model. -/
def unscalePoint (R : ℝ) {m : ℕ} (q : QuerySpace m) : QuerySpace m :=
  R⁻¹ • q

@[simp]
theorem unscalePoint_scalePoint {m : ℕ} {R : ℝ} (hR : R ≠ 0)
    (q : QuerySpace m) :
    unscalePoint R (scalePoint R q) = q := by
  simp [unscalePoint, scalePoint, hR]

@[simp]
theorem scalePoint_unscalePoint {m : ℕ} {R : ℝ} (hR : R ≠ 0)
    (q : QuerySpace m) :
    scalePoint R (unscalePoint R q) = q := by
  simp [unscalePoint, scalePoint, hR]

theorem scalePoint_mem_radiusBall {m : ℕ} {R : ℝ} (hR : 0 < R)
    {q : QuerySpace m} (hq : q ∈ unitBall m) :
    scalePoint R q ∈ radiusBall m R := by
  rw [radiusBall, mem_closedBall, dist_zero_right]
  rw [scalePoint, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_le_of_le_one_right hR.le (mem_unitBall_iff.mp hq)

theorem unscalePoint_mem_unitBall {m : ℕ} {R : ℝ} (hR : 0 < R)
    {q : QuerySpace m} (hq : q ∈ radiusBall m R) :
    unscalePoint R q ∈ unitBall m := by
  rw [mem_unitBall_iff]
  rw [unscalePoint, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have hnorm : ‖q‖ ≤ R := by
    simpa [radiusBall, mem_closedBall, dist_zero_right] using hq
  rw [inv_mul_le_one₀ hR]
  exact hnorm

/-! ## Exact transport to and from the unit model -/

/-- Simulate a radius-`R`, `L`-scale strategy in the unit model.  Unit oracle
answers are multiplied by `L * R` before being shown to the original strategy,
and its selected point is divided by `R`. -/
def toUnitStrategy {m : ℕ} {R : ℝ} (hR : 0 < R) (L : ℝ)
    (A : RadiusDeterministicStrategy m R) : DeterministicStrategy m where
  query ys := ⟨unscalePoint R (A.query (scaleAnswers (L * R) ys)),
    unscalePoint_mem_unitBall hR (A.query_mem_radiusBall _) ⟩
  output ys := ⟨unscalePoint R (A.output (scaleAnswers (L * R) ys)),
    unscalePoint_mem_unitBall hR (A.output_mem_radiusBall _) ⟩

/-- Simulate a unit strategy in the radius-`R`, `L`-scale model.  Scaled
answers are divided by `L * R` before being shown to the unit strategy. -/
def fromUnitStrategy {m : ℕ} {R : ℝ} (hR : 0 < R) (L : ℝ)
    (A : DeterministicStrategy m) : RadiusDeterministicStrategy m R where
  query ys := ⟨scalePoint R (A.query (scaleAnswers (L * R)⁻¹ ys)),
    scalePoint_mem_radiusBall hR (A.query_mem_unitBall _) ⟩
  output ys := ⟨scalePoint R (A.output (scaleAnswers (L * R)⁻¹ ys)),
    scalePoint_mem_radiusBall hR (A.output_mem_unitBall _) ⟩

@[simp]
theorem toUnitStrategy_query {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    ((toUnitStrategy hR L A).query ys : QuerySpace m) =
      unscalePoint R (A.query (scaleAnswers (L * R) ys)) := rfl

@[simp]
theorem toUnitStrategy_output {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    ((toUnitStrategy hR L A).output ys : QuerySpace m) =
      unscalePoint R (A.output (scaleAnswers (L * R) ys)) := rfl

theorem toUnitStrategy_queryAt {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ) (t : ℕ) :
    ((toUnitStrategy hR L A).queryAt ys t : QuerySpace m) =
      unscalePoint R (A.queryAt (scaleAnswers (L * R) ys) t) := by
  simp [DeterministicStrategy.queryAt, RadiusDeterministicStrategy.queryAt]

@[simp]
theorem fromUnitStrategy_query {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : DeterministicStrategy m) (ys : List ℝ) :
    ((fromUnitStrategy hR L A).query ys : QuerySpace m) =
      scalePoint R (A.query (scaleAnswers (L * R)⁻¹ ys)) := rfl

@[simp]
theorem fromUnitStrategy_output {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : DeterministicStrategy m) (ys : List ℝ) :
    ((fromUnitStrategy hR L A).output ys : QuerySpace m) =
      scalePoint R (A.output (scaleAnswers (L * R)⁻¹ ys)) := rfl

theorem fromUnitStrategy_queryAt {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : DeterministicStrategy m) (ys : List ℝ) (t : ℕ) :
    ((fromUnitStrategy hR L A).queryAt ys t : QuerySpace m) =
      scalePoint R (A.queryAt (scaleAnswers (L * R)⁻¹ ys) t) := by
  simp [DeterministicStrategy.queryAt, RadiusDeterministicStrategy.queryAt]

/-- Pointwise query round trip from the unit model through the scaled model. -/
theorem toUnit_fromUnitStrategy_query {m : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (A : DeterministicStrategy m)
    (ys : List ℝ) :
    ((toUnitStrategy hR L (fromUnitStrategy hR L A)).query ys : QuerySpace m) =
      (A.query ys : QuerySpace m) := by
  rw [toUnitStrategy_query, fromUnitStrategy_query,
    scaleAnswers_inv_scaleAnswers (mul_ne_zero hL.ne' hR.ne'),
    unscalePoint_scalePoint hR.ne']

/-- Pointwise output round trip from the unit model through the scaled model. -/
theorem toUnit_fromUnitStrategy_output {m : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (A : DeterministicStrategy m)
    (ys : List ℝ) :
    ((toUnitStrategy hR L (fromUnitStrategy hR L A)).output ys : QuerySpace m) =
      (A.output ys : QuerySpace m) := by
  rw [toUnitStrategy_output, fromUnitStrategy_output,
    scaleAnswers_inv_scaleAnswers (mul_ne_zero hL.ne' hR.ne'),
    unscalePoint_scalePoint hR.ne']

/-- Pointwise query round trip from the scaled model through the unit model. -/
theorem fromUnit_toUnitStrategy_query {m : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (A : RadiusDeterministicStrategy m R)
    (ys : List ℝ) :
    ((fromUnitStrategy hR L (toUnitStrategy hR L A)).query ys : QuerySpace m) =
      (A.query ys : QuerySpace m) := by
  rw [fromUnitStrategy_query, toUnitStrategy_query,
    scaleAnswers_scaleAnswers_inv (mul_ne_zero hL.ne' hR.ne'),
    scalePoint_unscalePoint hR.ne']

/-- Pointwise output round trip from the scaled model through the unit model. -/
theorem fromUnit_toUnitStrategy_output {m : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (A : RadiusDeterministicStrategy m R)
    (ys : List ℝ) :
    ((fromUnitStrategy hR L (toUnitStrategy hR L A)).output ys : QuerySpace m) =
      (A.output ys : QuerySpace m) := by
  rw [fromUnitStrategy_output, toUnitStrategy_output,
    scaleAnswers_scaleAnswers_inv (mul_ne_zero hL.ne' hR.ne'),
    scalePoint_unscalePoint hR.ne']

/-! ## The scaled hard objective -/

/-- The paper's radius/Lipschitz rescaling of the hard objective. -/
def scaledHardObjective {m : ℕ} [NeZero m]
    (R L : ℝ) (W : RowMatrix m) (q : QuerySpace m) : ℝ :=
  (L * R) * hardObjective W (unscalePoint R q)

@[simp]
theorem scaledHardObjective_zero {m : ℕ} [NeZero m]
    (R L : ℝ) (W : RowMatrix m) :
    scaledHardObjective R L W 0 = 0 := by
  simp [scaledHardObjective, unscalePoint]

theorem convexOn_scaledHardObjective {m : ℕ} [NeZero m]
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (W : RowMatrix m) :
    ConvexOn ℝ Set.univ (scaledHardObjective R L W) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hconv := (convexOn_hardObjective W).2
    (x := unscalePoint R x) (y := unscalePoint R y)
    (by simp) (by simp) hu hv huv
  change (L * R) * hardObjective W (unscalePoint R (u • x + v • y)) ≤ _
  rw [show unscalePoint R (u • x + v • y) =
      u • unscalePoint R x + v • unscalePoint R y by
        simp [unscalePoint, smul_add, smul_smul, mul_comm]]
  have hc : 0 ≤ L * R := (mul_pos hL hR).le
  calc
    (L * R) * hardObjective W
        (u • unscalePoint R x + v • unscalePoint R y) ≤
        (L * R) *
          (u * hardObjective W (unscalePoint R x) +
            v * hardObjective W (unscalePoint R y)) :=
      mul_le_mul_of_nonneg_left hconv hc
    _ = u * scaledHardObjective R L W x +
        v * scaledHardObjective R L W y := by
      simp [scaledHardObjective]
      ring

theorem scaledHardObjective_lipschitzWith {m : ℕ} [NeZero m]
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (W : RowMatrix m) (hW : Admissible W) :
    LipschitzWith ⟨L, hL.le⟩ (scaledHardObjective R L W) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hunit := (hardObjective_lipschitzWith_one W hW).dist_le_mul
    (unscalePoint R x) (unscalePoint R y)
  have hc : 0 ≤ L * R := (mul_pos hL hR).le
  calc
    dist (scaledHardObjective R L W x) (scaledHardObjective R L W y) =
        (L * R) *
          dist (hardObjective W (unscalePoint R x))
            (hardObjective W (unscalePoint R y)) := by
      rw [Real.dist_eq, Real.dist_eq]
      change
        |(L * R) * hardObjective W (unscalePoint R x) -
            (L * R) * hardObjective W (unscalePoint R y)| = _
      rw [← mul_sub, abs_mul, abs_of_pos (mul_pos hL hR)]
    _ ≤ (L * R) * dist (unscalePoint R x) (unscalePoint R y) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hunit) hc
    _ = L * dist x y := by
      rw [show dist (unscalePoint R x) (unscalePoint R y) =
          R⁻¹ * dist x y by
        unfold unscalePoint
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]]
      calc
        (L * R) * (R⁻¹ * dist x y) =
            L * (R * R⁻¹) * dist x y := by ring
        _ = L * dist x y := by rw [mul_inv_cancel₀ hR.ne', mul_one]

/-- The optimizer of the scaled objective is the radius-rescaled unit
optimizer. -/
def scaledHardOptimizer {m : ℕ} [NeZero m] (R : ℝ) (W : RowMatrix m) :
    QuerySpace m :=
  scalePoint R (hardOptimizer W)

theorem scaledHardOptimizer_mem_radiusBall {m : ℕ} [NeZero m]
    {R : ℝ} (hR : 0 < R) (W : RowMatrix m) :
    scaledHardOptimizer R W ∈ radiusBall m R :=
  scalePoint_mem_radiusBall hR (hardOptimizer_mem_unitBall W)

theorem isMinOn_scaledHardObjective {m : ℕ} [NeZero m]
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (W : RowMatrix m) :
    IsMinOn (scaledHardObjective R L W) (radiusBall m R)
      (scaledHardOptimizer R W) := by
  intro q hq
  change scaledHardObjective R L W (scaledHardOptimizer R W) ≤
    scaledHardObjective R L W q
  have hunit : unscalePoint R q ∈ unitBall m :=
    unscalePoint_mem_unitBall hR hq
  have hmin := (hardOptimizer_isMinOn W) hunit
  change (L * R) * hardObjective W
      (unscalePoint R (scalePoint R (hardOptimizer W))) ≤
    (L * R) * hardObjective W (unscalePoint R q)
  rw [unscalePoint_scalePoint hR.ne']
  exact mul_le_mul_of_nonneg_left hmin (mul_pos hL hR).le

theorem scaledHardObjective_gap {m : ℕ} [NeZero m]
    {R : ℝ} (hR : 0 < R) (L : ℝ) (W : RowMatrix m)
    (q : QuerySpace m) :
    scaledHardObjective R L W q -
        scaledHardObjective R L W (scaledHardOptimizer R W) =
      (L * R) *
        (hardObjective W (unscalePoint R q) -
          hardObjective W (hardOptimizer W)) := by
  simp [scaledHardObjective, scaledHardOptimizer,
    unscalePoint_scalePoint hR.ne']
  ring

/-! ## Consistency and objective-gap transport -/

theorem radiusConsistent_scaleAnswers_of_consistent
    {m : ℕ} [NeZero m] {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) {ys : List ℝ} {W : RowMatrix m}
    (hys : Consistent (toUnitStrategy hR L A) ys W) :
    RadiusConsistent A (scaleAnswers (L * R) ys) (scaledHardObjective R L W) := by
  intro t ht
  have ht' : t < ys.length := by simpa using ht
  have hu := hys t ht'
  rw [toUnitStrategy_queryAt hR A ys t] at hu
  rw [getElem_scaleAnswers (L * R) ys t ht']
  exact congrArg (fun y : ℝ ↦ (L * R) * y) hu

/-- The inverse exact-consistency transport.  A transcript for the scaled
simulation becomes a unit transcript after every answer is divided by
`L * R`. -/
theorem consistent_scaleAnswers_inv_of_radiusConsistent
    {m : ℕ} [NeZero m] {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (A : DeterministicStrategy m) {ys : List ℝ} {W : RowMatrix m}
    (hys : RadiusConsistent (fromUnitStrategy hR L A) ys
      (scaledHardObjective R L W)) :
    Consistent A (scaleAnswers (L * R)⁻¹ ys) W := by
  intro t ht
  have ht' : t < ys.length := by simpa using ht
  have hs := hys t ht'
  rw [fromUnitStrategy_queryAt hR A ys t] at hs
  change (L * R) * hardObjective W
      (unscalePoint R
        (scalePoint R
          (A.queryAt (scaleAnswers (L * R)⁻¹ ys) t : QuerySpace m))) = ys[t] at hs
  rw [unscalePoint_scalePoint hR.ne'] at hs
  rw [getElem_scaleAnswers (L * R)⁻¹ ys t ht']
  calc
    hardObjective W
        (A.queryAt (scaleAnswers (L * R)⁻¹ ys) t : QuerySpace m) =
        (L * R)⁻¹ *
          ((L * R) * hardObjective W
            (A.queryAt (scaleAnswers (L * R)⁻¹ ys) t : QuerySpace m)) := by
      rw [inv_mul_cancel_left₀ (mul_ne_zero hL.ne' hR.ne')]
    _ = (L * R)⁻¹ * ys[t] := by rw [hs]

theorem scaled_output_unscales_to_unit_output
    {m : ℕ} {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ) :
    unscalePoint R
        (A.output (scaleAnswers (L * R) ys) : QuerySpace m) =
      ((toUnitStrategy hR L A).output ys : QuerySpace m) := rfl

theorem scaledHardObjective_output_gap
    {m : ℕ} [NeZero m] {R L : ℝ} (hR : 0 < R)
    (A : RadiusDeterministicStrategy m R) (ys : List ℝ) (W : RowMatrix m) :
    scaledHardObjective R L W
          (A.output (scaleAnswers (L * R) ys) : QuerySpace m) -
        scaledHardObjective R L W (scaledHardOptimizer R W) =
      (L * R) *
        (hardObjective W
            ((toUnitStrategy hR L A).output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W)) := by
  rw [scaledHardObjective_gap hR]
  rfl

/-! ## Conditional scaled fixed-horizon endpoint -/

/-- Any unit-ball fixed-horizon lower bound transports verbatim to radius `R`
and Lipschitz constant `L`, with its accuracy multiplied by `L * R`.

The premise is deliberately only the semantic core of the unit endpoint.  The
scaled conclusion restores all objective-class certificates directly from the
hard-family lemmas above. -/
theorem scaledFixedHorizonLowerBound_strict_of_unit
    {m T : ℕ} [NeZero m] {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hunit : ∀ A : DeterministicStrategy m,
      ∃ ys : List ℝ, ∃ W : RowMatrix m,
        ys.length = T ∧
        Admissible W ∧
        Consistent A ys W ∧
        hardOptimizer W ∈ unitBall m ∧
        IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) ∧
        ε < hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W))
    (A : RadiusDeterministicStrategy m R) :
    ∃ zs : List ℝ, ∃ W : RowMatrix m,
      zs.length = T ∧
      Admissible W ∧
      scaledHardObjective R L W 0 = 0 ∧
      ConvexOn ℝ Set.univ (scaledHardObjective R L W) ∧
      LipschitzWith ⟨L, hL.le⟩ (scaledHardObjective R L W) ∧
      RadiusConsistent A zs (scaledHardObjective R L W) ∧
      scaledHardOptimizer R W ∈ radiusBall m R ∧
      IsMinOn (scaledHardObjective R L W) (radiusBall m R)
        (scaledHardOptimizer R W) ∧
      (L * R) * ε <
        scaledHardObjective R L W (A.output zs : QuerySpace m) -
          scaledHardObjective R L W (scaledHardOptimizer R W) := by
  obtain ⟨ys, W, hlen, hW, hcons, _, _, hgap⟩ :=
    hunit (toUnitStrategy hR L A)
  refine ⟨scaleAnswers (L * R) ys, W, ?_, hW,
    scaledHardObjective_zero R L W,
    convexOn_scaledHardObjective hR hL W,
    scaledHardObjective_lipschitzWith hR hL W hW,
    radiusConsistent_scaleAnswers_of_consistent hR A hcons,
    scaledHardOptimizer_mem_radiusBall hR W,
    isMinOn_scaledHardObjective hR hL W, ?_⟩
  · simpa using hlen
  · rw [scaledHardObjective_output_gap hR]
    exact mul_lt_mul_of_pos_left hgap (mul_pos hL hR)

end ZeroOrderBounds.AccuracyImprovement
