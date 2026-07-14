import ZeroOrderBounds.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# The finite max-linear hard family

For `m > 0`, a row matrix `W` determines `m` slopes in `QuerySpace m`.  The
`i`-th slope has first block `a e_i` and second block `W i`; the hard objective
is the maximum of the corresponding linear functionals.  This file establishes
the elementary convexity and Lipschitz facts used by the lower-bound argument.
-/

noncomputable section

open scoped BigOperators NNReal

namespace ZeroOrderBounds

/-- A matrix represented by its `m` rows in `RowSpace m`. -/
abbrev RowMatrix (m : ℕ) := Fin m → RowSpace m

/-- Every perturbation row lies in the radius-`tau m` Euclidean ball. -/
def Admissible {m : ℕ} (W : RowMatrix m) : Prop :=
  ∀ i, ‖W i‖ ≤ tau m

/-- The `i`-th standard Euclidean basis vector in the row space. -/
def basisVector {m : ℕ} (i : Fin m) : RowSpace m :=
  EuclideanSpace.single i 1

@[simp]
theorem basisVector_apply {m : ℕ} (i j : Fin m) :
    basisVector i j = if j = i then 1 else 0 := by
  simp [basisVector]

@[simp]
theorem norm_basisVector {m : ℕ} (i : Fin m) : ‖basisVector i‖ = 1 := by
  simp [basisVector]

/-- The full `2m`-dimensional slope associated with row `i`. -/
def slope {m : ℕ} (W : RowMatrix m) (i : Fin m) : QuerySpace m :=
  joinBlocks (a • basisVector i) (W i)

@[simp]
theorem firstBlock_slope {m : ℕ} (W : RowMatrix m) (i : Fin m) :
    firstBlock (slope W i) = a • basisVector i := by
  simp [slope]

@[simp]
theorem secondBlock_slope {m : ℕ} (W : RowMatrix m) (i : Fin m) :
    secondBlock (slope W i) = W i := by
  simp [slope]

@[simp]
theorem firstBlock_slope_apply {m : ℕ} (W : RowMatrix m) (i j : Fin m) :
    firstBlock (slope W i) j = if j = i then a else 0 := by
  simp [firstBlock_slope]

@[simp]
theorem secondBlock_slope_apply {m : ℕ} (W : RowMatrix m) (i j : Fin m) :
    secondBlock (slope W i) j = W i j := by
  simp

/-- Pythagoras for a hard-family slope. -/
theorem slope_norm_sq {m : ℕ} (W : RowMatrix m) (i : Fin m) :
    ‖slope W i‖ ^ 2 = a ^ 2 + ‖W i‖ ^ 2 := by
  rw [slope, joinBlocks_norm_sq]
  simp [norm_smul, a]

/-- Inner products split over the two Euclidean blocks. -/
theorem inner_joinBlocks {m : ℕ} (x z : RowSpace m) (q : QuerySpace m) :
    inner ℝ (joinBlocks x z) q =
      inner ℝ x (firstBlock q) + inner ℝ z (secondBlock q) := by
  simp [PiLp.inner_apply, joinBlocks, firstBlock, secondBlock, Fintype.sum_sum_type]

/-- Explicit max-affine row formula. -/
theorem inner_slope {m : ℕ} (W : RowMatrix m) (i : Fin m) (q : QuerySpace m) :
    inner ℝ (slope W i) q =
      a * firstBlock q i + inner ℝ (W i) (secondBlock q) := by
  have hsingle : inner ℝ (basisVector i) (firstBlock q) = firstBlock q i := by
    simpa [basisVector] using
      (EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (firstBlock q))
  rw [slope, inner_joinBlocks]
  rw [real_inner_smul_left, hsingle]

/-- The linear functional contributed by one row. -/
def rowValue {m : ℕ} (W : RowMatrix m) (i : Fin m) (q : QuerySpace m) : ℝ :=
  inner ℝ (slope W i) q

@[simp]
theorem rowValue_zero {m : ℕ} (W : RowMatrix m) (i : Fin m) :
    rowValue W i 0 = 0 := by
  simp [rowValue]

/-- The hard objective: the finite maximum of all row linear functionals.

The `NeZero m` instance records that there is at least one row, so `sup'` has
no arbitrary empty-family default value.
-/
def hardObjective {m : ℕ} [NeZero m] (W : RowMatrix m) (q : QuerySpace m) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty fun i ↦ rowValue W i q

/-- Every row value is bounded above by the hard objective. -/
theorem rowValue_le_hardObjective {m : ℕ} [NeZero m] (W : RowMatrix m)
    (i : Fin m) (q : QuerySpace m) :
    rowValue W i q ≤ hardObjective W q := by
  exact Finset.le_sup' (fun j ↦ rowValue W j q) (Finset.mem_univ i)

/-- A common upper bound on the row values bounds the hard objective. -/
theorem hardObjective_le {m : ℕ} [NeZero m] (W : RowMatrix m)
    (q : QuerySpace m) {r : ℝ} (h : ∀ i, rowValue W i q ≤ r) :
    hardObjective W q ≤ r := by
  exact Finset.sup'_le Finset.univ_nonempty _ fun i _ ↦ h i

@[simp]
theorem hardObjective_zero {m : ℕ} [NeZero m] (W : RowMatrix m) :
    hardObjective W 0 = 0 := by
  apply le_antisymm
  · exact hardObjective_le W 0 fun i ↦ (rowValue_zero W i).le
  · obtain ⟨i⟩ := (inferInstance : Nonempty (Fin m))
    simpa using rowValue_le_hardObjective W i 0

/-- The finite maximum of linear row values is convex on the whole query space. -/
theorem convexOn_hardObjective {m : ℕ} [NeZero m] (W : RowMatrix m) :
    ConvexOn ℝ Set.univ (hardObjective W) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  apply hardObjective_le W
  intro i
  calc
    rowValue W i (u • x + v • y) = u * rowValue W i x + v * rowValue W i y := by
      simp [rowValue, inner_add_right, inner_smul_right]
    _ ≤ u * hardObjective W x + v * hardObjective W y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (rowValue_le_hardObjective W i x) hu)
        (mul_le_mul_of_nonneg_left (rowValue_le_hardObjective W i y) hv)

/-- An inner-product functional has Lipschitz constant equal to the vector norm. -/
theorem lipschitzWith_inner {m : ℕ} (p : QuerySpace m) :
    LipschitzWith ‖p‖₊ (fun q : QuerySpace m ↦ inner ℝ p q) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, ← inner_sub_right]
  calc
    |inner ℝ p (x - y)| ≤ ‖p‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = (‖p‖₊ : ℝ) * dist x y := by simp [dist_eq_norm]

/-- A reusable finite-maximum rule for equally Lipschitz real-valued functions. -/
theorem lipschitzWith_finset_sup' {α ι : Type*} [PseudoMetricSpace α]
    (K : ℝ≥0) (s : Finset ι) (hs : s.Nonempty) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) :
    LipschitzWith K (fun x ↦ s.sup' hs fun i ↦ f i x) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let F : α → ℝ := fun z ↦ s.sup' hs fun i ↦ f i z
  have hxy : F x ≤ F y + (K : ℝ) * dist x y := by
    apply Finset.sup'_le hs
    intro i hi
    have hLip := (hf i hi).dist_le_mul x y
    rw [Real.dist_eq] at hLip
    calc
      f i x ≤ f i y + (K : ℝ) * dist x y := by
        nlinarith [le_abs_self (f i x - f i y)]
      _ ≤ F y + (K : ℝ) * dist x y := by
        gcongr
        exact Finset.le_sup' (fun j ↦ f j y) hi
  have hyx : F y ≤ F x + (K : ℝ) * dist x y := by
    apply Finset.sup'_le hs
    intro i hi
    have hLip := (hf i hi).dist_le_mul y x
    rw [Real.dist_eq, dist_comm y x] at hLip
    calc
      f i y ≤ f i x + (K : ℝ) * dist x y := by
        nlinarith [le_abs_self (f i y - f i x)]
      _ ≤ F x + (K : ℝ) * dist x y := by
        gcongr
        exact Finset.le_sup' (fun j ↦ f j x) hi
  change dist (F x) (F y) ≤ (K : ℝ) * dist x y
  rw [Real.dist_eq]
  exact (abs_le.2 ⟨by linarith, by linarith⟩)

/-- For positive dimension, the uncertainty radius is at most `1/200`. -/
theorem tau_le_one_div_two_hundred {m : ℕ} (hm : 1 ≤ m) :
    tau m ≤ (1 : ℝ) / 200 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := (Real.one_le_sqrt).2 hm'
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := zero_lt_one.trans_le hsqrt
  rw [tau, a, Gamma, div_le_iff₀ (mul_pos (by norm_num) hsqrt_pos)]
  nlinarith

/-- Every admissible slope has Euclidean norm at most one. -/
theorem norm_slope_le_one_of_admissible {m : ℕ} (hm : 1 ≤ m)
    (W : RowMatrix m) (hW : Admissible W) (i : Fin m) :
    ‖slope W i‖ ≤ 1 := by
  have hw_nonneg : 0 ≤ ‖W i‖ := norm_nonneg _
  have hw : ‖W i‖ ≤ (1 : ℝ) / 200 :=
    (hW i).trans (tau_le_one_div_two_hundred hm)
  have hw_sq : ‖W i‖ ^ 2 ≤ ((1 : ℝ) / 200) ^ 2 := by
    nlinarith [sq_nonneg ((1 : ℝ) / 200 - ‖W i‖)]
  have hslope_nonneg : 0 ≤ ‖slope W i‖ := norm_nonneg _
  have hslope_sq := slope_norm_sq W i
  norm_num [a] at hslope_sq
  nlinarith

/-- Admissible hard objectives in every positive dimension are globally one-Lipschitz. -/
theorem hardObjective_lipschitzWith_one {m : ℕ} [NeZero m]
    (W : RowMatrix m) (hW : Admissible W) :
    LipschitzWith 1 (hardObjective W) := by
  apply lipschitzWith_finset_sup' 1 Finset.univ Finset.univ_nonempty
  intro i _
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hnorm : ‖slope W i‖₊ ≤ (1 : ℝ≥0) := by
    exact_mod_cast norm_slope_le_one_of_admissible hm W hW i
  exact (lipschitzWith_inner (slope W i)).weaken hnorm

end ZeroOrderBounds
