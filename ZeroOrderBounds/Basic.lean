import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Basic Euclidean infrastructure

This module fixes the ambient Euclidean spaces and elementary block-coordinate
operations used by the zeroth-order lower-bound construction.  In particular,
`QuerySpace m` is a single Euclidean space indexed by a sum type; it does not
use the supremum norm on an ordinary product.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds

/-- The Euclidean space containing one row of the hard instance. -/
abbrev RowSpace (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The Euclidean query space, with two `m`-dimensional blocks and the `ℓ²` norm. -/
abbrev QuerySpace (m : ℕ) := EuclideanSpace ℝ (Fin m ⊕ Fin m)

/-- The first block of a query vector. -/
def firstBlock {m : ℕ} (q : QuerySpace m) : RowSpace m :=
  WithLp.toLp 2 fun i ↦ q (Sum.inl i)

/-- The second block of a query vector. -/
def secondBlock {m : ℕ} (q : QuerySpace m) : RowSpace m :=
  WithLp.toLp 2 fun i ↦ q (Sum.inr i)

/-- Join two `m`-dimensional blocks into the ambient `2m`-dimensional query space. -/
def joinBlocks {m : ℕ} (x z : RowSpace m) : QuerySpace m :=
  WithLp.toLp 2 fun
    | Sum.inl i => x i
    | Sum.inr i => z i

@[simp]
theorem firstBlock_apply {m : ℕ} (q : QuerySpace m) (i : Fin m) :
    firstBlock q i = q (Sum.inl i) :=
  rfl

@[simp]
theorem secondBlock_apply {m : ℕ} (q : QuerySpace m) (i : Fin m) :
    secondBlock q i = q (Sum.inr i) :=
  rfl

@[simp]
theorem joinBlocks_apply_inl {m : ℕ} (x z : RowSpace m) (i : Fin m) :
    joinBlocks x z (Sum.inl i) = x i :=
  rfl

@[simp]
theorem joinBlocks_apply_inr {m : ℕ} (x z : RowSpace m) (i : Fin m) :
    joinBlocks x z (Sum.inr i) = z i :=
  rfl

@[simp]
theorem firstBlock_joinBlocks {m : ℕ} (x z : RowSpace m) :
    firstBlock (joinBlocks x z) = x := by
  ext i
  rfl

@[simp]
theorem secondBlock_joinBlocks {m : ℕ} (x z : RowSpace m) :
    secondBlock (joinBlocks x z) = z := by
  ext i
  rfl

@[simp]
theorem joinBlocks_firstBlock_secondBlock {m : ℕ} (q : QuerySpace m) :
    joinBlocks (firstBlock q) (secondBlock q) = q := by
  ext i
  cases i <;> rfl

/-- The squared Euclidean norm is the sum of the squared block norms. -/
theorem joinBlocks_norm_sq {m : ℕ} (x z : RowSpace m) :
    ‖joinBlocks x z‖ ^ 2 = ‖x‖ ^ 2 + ‖z‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]

/-- Splitting a query into blocks gives the Pythagorean identity. -/
theorem norm_sq_eq_firstBlock_add_secondBlock {m : ℕ} (q : QuerySpace m) :
    ‖q‖ ^ 2 = ‖firstBlock q‖ ^ 2 + ‖secondBlock q‖ ^ 2 := by
  rw [← joinBlocks_norm_sq (firstBlock q) (secondBlock q)]
  simp

/-- Projecting to the first block cannot increase the Euclidean norm. -/
theorem norm_firstBlock_le {m : ℕ} (q : QuerySpace m) : ‖firstBlock q‖ ≤ ‖q‖ := by
  have hsq : ‖firstBlock q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [norm_sq_eq_firstBlock_add_secondBlock]
    exact le_add_of_nonneg_right (sq_nonneg ‖secondBlock q‖)
  nlinarith [norm_nonneg (firstBlock q), norm_nonneg q]

/-- Projecting to the second block cannot increase the Euclidean norm. -/
theorem norm_secondBlock_le {m : ℕ} (q : QuerySpace m) : ‖secondBlock q‖ ≤ ‖q‖ := by
  have hsq : ‖secondBlock q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [norm_sq_eq_firstBlock_add_secondBlock]
    exact le_add_of_nonneg_left (sq_nonneg ‖firstBlock q‖)
  nlinarith [norm_nonneg (secondBlock q), norm_nonneg q]

/-- The closed Euclidean unit ball in the query space. -/
def unitBall (m : ℕ) : Set (QuerySpace m) :=
  Metric.closedBall 0 1

@[simp]
theorem mem_unitBall_iff {m : ℕ} {q : QuerySpace m} :
    q ∈ unitBall m ↔ ‖q‖ ≤ 1 := by
  simp [unitBall]

/-- The fixed first-block slope used in the hard max-affine family. -/
def a : ℝ := 1 / 2

/-- Slack constant used to set the uncertainty radius. -/
def Gamma : ℝ := 100

/-- Radius of each initial row-uncertainty ball. -/
def tau (m : ℕ) : ℝ :=
  a / (Gamma * Real.sqrt (m : ℝ))

theorem a_pos : 0 < a := by
  norm_num [a]

theorem Gamma_pos : 0 < Gamma := by
  norm_num [Gamma]

theorem tau_pos {m : ℕ} (hm : 0 < m) : 0 < tau m := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact div_pos a_pos (mul_pos Gamma_pos (Real.sqrt_pos.2 hm'))

/-- The sum of the coordinates in the first block of a query. -/
def coordinateSum {m : ℕ} (q : QuerySpace m) : ℝ :=
  ∑ i, firstBlock q i

@[simp]
theorem coordinateSum_zero (m : ℕ) :
    coordinateSum (0 : QuerySpace m) = 0 := by
  simp [coordinateSum]

@[simp]
theorem coordinateSum_add {m : ℕ} (q r : QuerySpace m) :
    coordinateSum (q + r) = coordinateSum q + coordinateSum r := by
  simp [coordinateSum, Finset.sum_add_distrib]

@[simp]
theorem coordinateSum_sub {m : ℕ} (q r : QuerySpace m) :
    coordinateSum (q - r) = coordinateSum q - coordinateSum r := by
  simp [coordinateSum, Finset.sum_sub_distrib]

@[simp]
theorem coordinateSum_smul {m : ℕ} (c : ℝ) (q : QuerySpace m) :
    coordinateSum (c • q) = c * coordinateSum q := by
  simp [coordinateSum, Finset.mul_sum]

/-- The all-ones vector in a row space. -/
def rowOnes (m : ℕ) : RowSpace m :=
  WithLp.toLp 2 fun _ ↦ (1 : ℝ)

@[simp]
theorem rowOnes_apply (m : ℕ) (i : Fin m) : rowOnes m i = 1 :=
  rfl

theorem norm_rowOnes (m : ℕ) : ‖rowOnes m‖ = Real.sqrt (m : ℝ) := by
  simp [EuclideanSpace.norm_eq, rowOnes]

/-- The coordinate sum is the inner product with the all-ones vector. -/
theorem coordinateSum_eq_inner {m : ℕ} (q : QuerySpace m) :
    coordinateSum q = inner ℝ (rowOnes m) (firstBlock q) := by
  simp [coordinateSum, rowOnes, PiLp.inner_apply]

/-- Cauchy--Schwarz bound for the first-block coordinate sum. -/
theorem abs_coordinateSum_le {m : ℕ} (q : QuerySpace m) :
    |coordinateSum q| ≤ Real.sqrt (m : ℝ) * ‖q‖ := by
  rw [coordinateSum_eq_inner]
  calc
    |inner ℝ (rowOnes m) (firstBlock q)| ≤ ‖rowOnes m‖ * ‖firstBlock q‖ :=
      abs_real_inner_le_norm _ _
    _ = Real.sqrt (m : ℝ) * ‖firstBlock q‖ := by rw [norm_rowOnes]
    _ ≤ Real.sqrt (m : ℝ) * ‖q‖ :=
      mul_le_mul_of_nonneg_left (norm_firstBlock_le q) (Real.sqrt_nonneg _)

end ZeroOrderBounds
