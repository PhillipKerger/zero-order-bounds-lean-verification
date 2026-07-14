import ZeroOrderBounds.HardFamily
import ZeroOrderBounds.IntrinsicVolume
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Deterministic exact-value strategies and oracle states

This file contains the information-theoretic part of the oracle model.  A
strategy is an entirely arbitrary pair of functions from finite lists of exact
real answers to points of the Euclidean unit ball.  No regularity or
computability hypothesis is imposed.

The geometric uncertainty at a round is a Cartesian product of compact convex
row bodies.  The central invariant, `ProductConsistent`, is deliberately
strong: *every* matrix selected from that product reproduces the whole exact
transcript.  The generic append lemma near the end of the file is the interface
used by the resisting-oracle update: it is enough to shrink every row body and
prove exactness at the new query.
-/

noncomputable section

open Metric
open scoped ENNReal

namespace ZeroOrderBounds

/-! ## Strategies, queries at transcript prefixes, and consistency -/

/-- A query point bundled with the proof that it belongs to the Euclidean unit ball. -/
abbrev UnitBall (m : ℕ) := {q : QuerySpace m // q ∈ unitBall m}

/-- An arbitrary deterministic exact-value strategy.

Both maps may be discontinuous and noncomputable.  The horizon is kept external
to the structure.
-/
structure DeterministicStrategy (m : ℕ) where
  query : List ℝ → UnitBall m
  output : List ℝ → UnitBall m

/-- Short name used in statements about the oracle recursion. -/
abbrev Strategy := DeterministicStrategy

namespace DeterministicStrategy

variable {m : ℕ}

/-- The query at round `t`, computed from exactly the first `t` answers. -/
def queryAt (A : DeterministicStrategy m) (ys : List ℝ) (t : ℕ) : UnitBall m :=
  A.query (ys.take t)

@[simp]
theorem queryAt_zero (A : DeterministicStrategy m) (ys : List ℝ) :
    A.queryAt ys 0 = A.query [] := by
  simp [queryAt]

/-- At the end of a transcript, `queryAt` is the strategy's next query. -/
@[simp]
theorem queryAt_length (A : DeterministicStrategy m) (ys : List ℝ) :
    A.queryAt ys ys.length = A.query ys := by
  simp [queryAt]

/-- Taking a longer prefix of a transcript does not affect an earlier query. -/
theorem queryAt_take (A : DeterministicStrategy m) (ys : List ℝ) {s t : ℕ}
    (hts : t ≤ s) :
    A.queryAt (ys.take s) t = A.queryAt ys t := by
  simp [queryAt, List.take_take, Nat.min_eq_left hts]

/-- Appending future answers does not affect a query made during the old transcript. -/
theorem queryAt_append_of_le_length (A : DeterministicStrategy m) (ys zs : List ℝ)
    {t : ℕ} (ht : t ≤ ys.length) :
    A.queryAt (ys ++ zs) t = A.queryAt ys t := by
  simp [queryAt, List.take_append_of_le_length ht]

@[simp]
theorem query_mem_unitBall (A : DeterministicStrategy m) (ys : List ℝ) :
    (A.query ys : QuerySpace m) ∈ unitBall m :=
  (A.query ys).property

@[simp]
theorem output_mem_unitBall (A : DeterministicStrategy m) (ys : List ℝ) :
    (A.output ys : QuerySpace m) ∈ unitBall m :=
  (A.output ys).property

theorem norm_query_le_one (A : DeterministicStrategy m) (ys : List ℝ) :
    ‖(A.query ys : QuerySpace m)‖ ≤ 1 :=
  mem_unitBall_iff.mp (A.query_mem_unitBall ys)

theorem norm_output_le_one (A : DeterministicStrategy m) (ys : List ℝ) :
    ‖(A.output ys : QuerySpace m)‖ ≤ 1 :=
  mem_unitBall_iff.mp (A.output_mem_unitBall ys)

end DeterministicStrategy

/-- A matrix `W` is consistent with `ys` when every answer is exactly the hard
objective at the deterministic query computed from the preceding prefix. -/
def Consistent {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (ys : List ℝ) (W : RowMatrix m) : Prop :=
  ∀ (t : ℕ) (ht : t < ys.length),
    hardObjective W (A.queryAt ys t : QuerySpace m) = ys[t]

namespace Consistent

variable {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
  {ys xs : List ℝ} {W : RowMatrix m}

@[simp]
theorem nil (A : DeterministicStrategy m) (W : RowMatrix m) :
    Consistent A [] W := by
  intro t ht
  simp at ht

/-- Consistency is inherited by every prefix obtained using `List.take`. -/
theorem take (h : Consistent A ys W) (n : ℕ) :
    Consistent A (ys.take n) W := by
  intro t ht
  have htmin : t < min n ys.length := by
    simpa using ht
  have htn : t ≤ n := Nat.le_of_lt (htmin.trans_le (min_le_left _ _))
  have hty : t < ys.length := htmin.trans_le (min_le_right _ _)
  rw [A.queryAt_take ys htn]
  rw [h t hty]
  exact List.getElem_take.symm

/-- Consistency is monotone under the list-prefix relation. -/
theorem of_isPrefix (h : Consistent A ys W) (hxy : xs <+: ys) :
    Consistent A xs W := by
  obtain ⟨zs, rfl⟩ := hxy
  simpa using h.take xs.length

/-- Exact consistency after one answer is equivalent to old consistency plus
exactness of the new answer at the next query. -/
theorem append_singleton_iff (y : ℝ) :
    Consistent A (ys ++ [y]) W ↔
      Consistent A ys W ∧ hardObjective W (A.query ys : QuerySpace m) = y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h.take ys.length
    · simpa [DeterministicStrategy.queryAt] using h ys.length (by simp)
  · rintro ⟨hold, hnew⟩ t ht
    by_cases hlt : t < ys.length
    · have hquery : A.queryAt (ys ++ [y]) t = A.queryAt ys t :=
        A.queryAt_append_of_le_length ys [y] hlt.le
      rw [hquery, hold t hlt]
      simp [hlt]
    · have htle : t ≤ ys.length := by simpa using ht
      have hteq : t = ys.length := Nat.le_antisymm htle (Nat.le_of_not_gt hlt)
      subst t
      simpa [DeterministicStrategy.queryAt] using hnew

theorem append_singleton (hold : Consistent A ys W)
    {y : ℝ} (hnew : hardObjective W (A.query ys : QuerySpace m) = y) :
    Consistent A (ys ++ [y]) W :=
  (append_singleton_iff y).2 ⟨hold, hnew⟩

end Consistent

/-! ## Compact convex row bodies and their Cartesian product -/

/-- A compact convex uncertainty body for one row.  Positivity is intrinsic to
its own affine hull (using the zero-dimensional convention from
`IntrinsicVolume`), while `subset_initial` records admissibility permanently. -/
structure RowBody (m : ℕ) where
  body : IntrinsicBody (RowSpace m)
  subset_initial : body.carrier ⊆ closedBall (0 : RowSpace m) (tau m)

namespace RowBody

variable {m : ℕ}

instance : SetLike (RowBody m) (RowSpace m) where
  coe P := P.body.carrier
  coe_injective := by
    intro P Q h
    cases P with
    | mk P hP =>
      cases Q with
      | mk Q hQ =>
        dsimp only at h
        have hPQ : P = Q := SetLike.coe_injective h
        subst Q
        rfl

@[simp]
theorem mem_carrier (P : RowBody m) (w : RowSpace m) :
    w ∈ P.body.carrier ↔ w ∈ P :=
  Iff.rfl

@[ext]
theorem ext {P Q : RowBody m} (h : (P : Set (RowSpace m)) = Q) : P = Q :=
  SetLike.coe_injective h

/-- Turn an intrinsic body contained in the initial ball into an oracle row body. -/
def ofIntrinsicBody (P : IntrinsicBody (RowSpace m))
    (hP : P.carrier ⊆ closedBall (0 : RowSpace m) (tau m)) : RowBody m where
  body := P
  subset_initial := hP

/-- Constructor used by later closed truncations and affine sections. -/
def ofCompactConvex (P : Set (RowSpace m)) (hne : P.Nonempty)
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    (hball : P ⊆ closedBall (0 : RowSpace m) (tau m)) : RowBody m :=
  ofIntrinsicBody (IntrinsicBody.ofCompactConvex P hne hcompact hconvex) hball

theorem nonempty (P : RowBody m) : ((P : Set (RowSpace m))).Nonempty :=
  P.body.nonempty

theorem isCompact (P : RowBody m) : IsCompact (P : Set (RowSpace m)) :=
  P.body.isCompact

theorem convex (P : RowBody m) : Convex ℝ (P : Set (RowSpace m)) :=
  P.body.convex

theorem volume_pos (P : RowBody m) : 0 < intrinsicVolume (P : Set (RowSpace m)) :=
  P.body.volume_pos

theorem volume_lt_top (P : RowBody m) : intrinsicVolume (P : Set (RowSpace m)) < ⊤ :=
  P.body.volume_lt_top

/-- Affine hull of a row body. -/
def hull (P : RowBody m) : AffineSubspace ℝ (RowSpace m) :=
  P.body.hull

/-- Intrinsic affine dimension of a row body. -/
def dim (P : RowBody m) : ℕ :=
  P.body.dim

/-- Intrinsic Hausdorff volume of a row body. -/
def volume (P : RowBody m) : ENNReal :=
  P.body.volume

/-- Real-valued intrinsic volume, for multiplicative potential estimates. -/
def volumeReal (P : RowBody m) : ℝ :=
  P.body.volumeReal

theorem volumeReal_pos (P : RowBody m) : 0 < P.volumeReal :=
  P.body.volumeReal_pos

theorem mem_initial_ball (P : RowBody m) {w : RowSpace m} (hw : w ∈ P) :
    w ∈ closedBall (0 : RowSpace m) (tau m) :=
  P.subset_initial hw

theorem norm_le_tau (P : RowBody m) {w : RowSpace m} (hw : w ∈ P) :
    ‖w‖ ≤ tau m := by
  simpa using P.mem_initial_ball hw

end RowBody

/-- The radius `tau` is nonnegative even in the degenerate zero-dimensional case. -/
theorem tau_nonneg (m : ℕ) : 0 ≤ tau m := by
  by_cases hm : m = 0
  · subst m
    norm_num [tau, a, Gamma]
  · exact (tau_pos (Nat.pos_of_ne_zero hm)).le

/-- The initial uncertainty body for every row. -/
def initialRowBody (m : ℕ) : RowBody m :=
  RowBody.ofCompactConvex
    (closedBall (0 : RowSpace m) (tau m))
    (nonempty_closedBall.mpr (tau_nonneg m))
    (isCompact_closedBall (0 : RowSpace m) (tau m))
    (convex_closedBall (0 : RowSpace m) (tau m))
    (fun _ hw ↦ hw)

namespace initialRowBody

@[simp]
theorem carrier (m : ℕ) :
    (initialRowBody m : Set (RowSpace m)) = closedBall 0 (tau m) :=
  rfl

theorem mem_iff {m : ℕ} {w : RowSpace m} :
    w ∈ initialRowBody m ↔ ‖w‖ ≤ tau m := by
  change w ∈ closedBall (0 : RowSpace m) (tau m) ↔ _
  simp [mem_closedBall, dist_eq_norm]

/-- The positive-radius initial ball spans the whole row space. -/
theorem hull_eq_top {m : ℕ} (hm : 0 < m) :
    (initialRowBody m).hull = ⊤ := by
  have hinterior :
      (interior (closedBall (0 : RowSpace m) (tau m))).Nonempty :=
    (nonempty_ball.mpr (tau_pos hm)).mono ball_subset_interior_closedBall
  exact (convex_closedBall (0 : RowSpace m) (tau m)).interior_nonempty_iff_affineSpan_eq_top.mp
    hinterior

/-- Initially every row body has the full ambient affine dimension. -/
theorem dim_eq {m : ℕ} (hm : 0 < m) : (initialRowBody m).dim = m := by
  have hspan := hull_eq_top hm
  unfold RowBody.hull IntrinsicBody.hull at hspan
  rw [RowBody.dim, IntrinsicBody.dim, affineDim, hspan]
  rw [AffineSubspace.direction_top, finrank_top]
  exact finrank_euclideanSpace_fin

end initialRowBody

/-- Predicate saying that `W` selects one point from each row body. -/
def IsRowSelection {m : ℕ} (rows : Fin m → RowBody m) (W : RowMatrix m) : Prop :=
  ∀ i, W i ∈ rows i

/-- The Cartesian product of a family of row bodies. -/
def rowProduct {m : ℕ} (rows : Fin m → RowBody m) : Set (RowMatrix m) :=
  {W | IsRowSelection rows W}

/-- A bundled selection from the Cartesian product. -/
abbrev RowSelection {m : ℕ} (rows : Fin m → RowBody m) :=
  {W : RowMatrix m // W ∈ rowProduct rows}

namespace RowSelection

variable {m : ℕ} {rows : Fin m → RowBody m}

@[simp]
theorem mem (W : RowSelection rows) (i : Fin m) : (W : RowMatrix m) i ∈ rows i :=
  W.property i

theorem admissible (W : RowSelection rows) : Admissible (W : RowMatrix m) :=
  fun i ↦ (rows i).norm_le_tau (W.property i)

end RowSelection

@[simp]
theorem mem_rowProduct {m : ℕ} {rows : Fin m → RowBody m} {W : RowMatrix m} :
    W ∈ rowProduct rows ↔ ∀ i, W i ∈ rows i :=
  Iff.rfl

theorem rowProduct_mono {m : ℕ} {oldRows newRows : Fin m → RowBody m}
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ oldRows i) :
    rowProduct newRows ⊆ rowProduct oldRows := by
  intro W hW i
  exact hsub i (hW i)

theorem rowProduct_nonempty {m : ℕ} (rows : Fin m → RowBody m) :
    (rowProduct rows).Nonempty := by
  classical
  choose W hW using fun i ↦ (rows i).nonempty
  exact ⟨W, hW⟩

theorem admissible_of_mem_rowProduct {m : ℕ} {rows : Fin m → RowBody m}
    {W : RowMatrix m} (hW : W ∈ rowProduct rows) : Admissible W := by
  intro i
  exact (rows i).norm_le_tau (hW i)

theorem initial_rowProduct_eq_admissible {m : ℕ} {W : RowMatrix m} :
    W ∈ rowProduct (fun _ ↦ initialRowBody m) ↔ Admissible W := by
  simp only [mem_rowProduct, initialRowBody.mem_iff, Admissible]

/-! ## Row evaluations and the simultaneous transcript invariant -/

/-- The affine value supplied by row `i` with perturbation vector `w` at `q`. -/
def rowEvaluation {m : ℕ} (q : QuerySpace m) (i : Fin m) (w : RowSpace m) : ℝ :=
  a * firstBlock q i + inner ℝ w (secondBlock q)

@[simp]
theorem rowEvaluation_matrix {m : ℕ} (q : QuerySpace m) (i : Fin m)
    (W : RowMatrix m) :
    rowEvaluation q i (W i) = rowValue W i q := by
  rw [rowEvaluation, rowValue, inner_slope]

/-- Rowwise condition ensuring that every matrix in a Cartesian product has
hard-objective value exactly `y` at `q`.  The equality witness is uniform over
one entire retained row body, as is the case for both oracle update branches. -/
def RowsAnswerAt {m : ℕ} (rows : Fin m → RowBody m) (q : QuerySpace m) (y : ℝ) : Prop :=
  (∀ i w, w ∈ rows i → rowEvaluation q i w ≤ y) ∧
    ∃ i, ∀ w, w ∈ rows i → rowEvaluation q i w = y

namespace RowsAnswerAt

variable {m : ℕ} {oldRows newRows : Fin m → RowBody m} {q : QuerySpace m} {y : ℝ}

/-- Rowwise exact-answer certificates persist when all row bodies shrink. -/
theorem mono (h : RowsAnswerAt oldRows q y)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ oldRows i) :
    RowsAnswerAt newRows q y := by
  rcases h with ⟨hle, i, heq⟩
  exact ⟨fun j w hw ↦ hle j w (hsub j hw), i, fun w hw ↦ heq w (hsub i hw)⟩

/-- A rowwise certificate computes the hard objective for any selected matrix. -/
theorem hardObjective_eq [NeZero m] (h : RowsAnswerAt newRows q y)
    {W : RowMatrix m} (hW : W ∈ rowProduct newRows) :
    hardObjective W q = y := by
  rcases h with ⟨hle, i, heq⟩
  apply le_antisymm
  · apply hardObjective_le W q
    intro j
    rw [← rowEvaluation_matrix q j W]
    exact hle j (W j) (hW j)
  · calc
      y = rowEvaluation q i (W i) := (heq (W i) (hW i)).symm
      _ = rowValue W i q := rowEvaluation_matrix q i W
      _ ≤ hardObjective W q := rowValue_le_hardObjective W i q

end RowsAnswerAt

/-- Strong invariant: every matrix in the current Cartesian product reproduces
the entire transcript, not merely the most recent answer. -/
def ProductConsistent {m : ℕ} [NeZero m] (A : DeterministicStrategy m)
    (ys : List ℝ) (rows : Fin m → RowBody m) : Prop :=
  ∀ {W : RowMatrix m}, W ∈ rowProduct rows → Consistent A ys W

namespace ProductConsistent

variable {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
  {ys xs : List ℝ} {rows oldRows newRows : Fin m → RowBody m}

@[simp]
theorem nil (A : DeterministicStrategy m) (rows : Fin m → RowBody m) :
    ProductConsistent A [] rows := by
  intro W hW
  exact Consistent.nil A W

theorem take (h : ProductConsistent A ys rows) (n : ℕ) :
    ProductConsistent A (ys.take n) rows := by
  intro W hW
  exact (h hW).take n

theorem of_isPrefix (h : ProductConsistent A ys rows) (hxy : xs <+: ys) :
    ProductConsistent A xs rows := by
  intro W hW
  exact (h hW).of_isPrefix hxy

/-- Shrinking row bodies preserves all exact answers already in the transcript. -/
theorem mono_rows (h : ProductConsistent A ys oldRows)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ oldRows i) :
    ProductConsistent A ys newRows := by
  intro W hW
  exact h (rowProduct_mono hsub hW)

/-- Generic one-step preservation theorem for the exact product invariant. -/
theorem append_of_subset (h : ProductConsistent A ys oldRows) (y : ℝ)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ oldRows i)
    (hcurrent : ∀ {W : RowMatrix m}, W ∈ rowProduct newRows →
      hardObjective W (A.query ys : QuerySpace m) = y) :
    ProductConsistent A (ys ++ [y]) newRows := by
  intro W hW
  exact Consistent.append_singleton (h (rowProduct_mono hsub hW)) (hcurrent hW)

/-- Rowwise form of `append_of_subset`, tailored to the output of an oracle cut. -/
theorem append_of_rowsAnswerAt (h : ProductConsistent A ys oldRows) (y : ℝ)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ oldRows i)
    (hanswer : RowsAnswerAt newRows (A.query ys : QuerySpace m) y) :
    ProductConsistent A (ys ++ [y]) newRows :=
  h.append_of_subset y hsub fun hW ↦ hanswer.hardObjective_eq hW

end ProductConsistent

/-! ## Bundled oracle states -/

/-- A resisting-oracle state, carrying the strong product invariant as a field. -/
structure OracleState {m : ℕ} [NeZero m] (A : DeterministicStrategy m) where
  answers : List ℝ
  rows : Fin m → RowBody m
  product_consistent : ProductConsistent A answers rows

namespace OracleState

variable {m : ℕ} [NeZero m] {A : DeterministicStrategy m}

/-- Number of completed exact-value rounds. -/
def round (S : OracleState A) : ℕ :=
  S.answers.length

/-- Query issued from the complete transcript stored in a state. -/
def nextQuery (S : OracleState A) : UnitBall m :=
  A.query S.answers

@[simp]
theorem nextQuery_eq (S : OracleState A) : S.nextQuery = A.query S.answers :=
  rfl

theorem every_selection_consistent (S : OracleState A) {W : RowMatrix m}
    (hW : W ∈ rowProduct S.rows) : Consistent A S.answers W :=
  S.product_consistent hW

theorem every_selection_admissible (S : OracleState A) {W : RowMatrix m}
    (hW : W ∈ rowProduct S.rows) : Admissible W :=
  admissible_of_mem_rowProduct hW

theorem product_nonempty (S : OracleState A) : (rowProduct S.rows).Nonempty :=
  rowProduct_nonempty S.rows

/-- Build a successor state after shrinking every row body and proving a common
exact value at the state's next query.  Oracle geometry is intentionally absent
from this constructor. -/
def extend (S : OracleState A) (newRows : Fin m → RowBody m) (y : ℝ)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ S.rows i)
    (hcurrent : ∀ {W : RowMatrix m}, W ∈ rowProduct newRows →
      hardObjective W (S.nextQuery : QuerySpace m) = y) : OracleState A where
  answers := S.answers ++ [y]
  rows := newRows
  product_consistent :=
    ProductConsistent.append_of_subset S.product_consistent y hsub
      (fun {W} hW ↦ by simpa [nextQuery] using hcurrent (W := W) hW)

/-- Successor-state constructor using a rowwise exact-answer certificate. -/
def extendOfRowsAnswerAt (S : OracleState A) (newRows : Fin m → RowBody m) (y : ℝ)
    (hsub : ∀ i, (newRows i : Set (RowSpace m)) ⊆ S.rows i)
    (hanswer : RowsAnswerAt newRows (S.nextQuery : QuerySpace m) y) : OracleState A :=
  S.extend newRows y hsub fun hW ↦ hanswer.hardObjective_eq hW

@[simp]
theorem extend_answers (S : OracleState A) (newRows : Fin m → RowBody m) (y : ℝ)
    (hsub) (hcurrent) :
    (S.extend newRows y hsub hcurrent).answers = S.answers ++ [y] :=
  rfl

@[simp]
theorem extend_rows (S : OracleState A) (newRows : Fin m → RowBody m) (y : ℝ)
    (hsub) (hcurrent) :
    (S.extend newRows y hsub hcurrent).rows = newRows :=
  rfl

@[simp]
theorem round_extend (S : OracleState A) (newRows : Fin m → RowBody m) (y : ℝ)
    (hsub) (hcurrent) :
    (S.extend newRows y hsub hcurrent).round = S.round + 1 := by
  simp [round]

/-- The initial state has empty transcript and the full admissible row balls. -/
def initial (A : DeterministicStrategy m) : OracleState A where
  answers := []
  rows := fun _ ↦ initialRowBody m
  product_consistent := ProductConsistent.nil A _

@[simp]
theorem initial_answers (A : DeterministicStrategy m) : (initial A).answers = [] :=
  rfl

@[simp]
theorem initial_rows (A : DeterministicStrategy m) (i : Fin m) :
    (initial A).rows i = initialRowBody m :=
  rfl

@[simp]
theorem round_initial (A : DeterministicStrategy m) : (initial A).round = 0 :=
  rfl

theorem initial_product_eq_admissible (A : DeterministicStrategy m) (W : RowMatrix m) :
    W ∈ rowProduct (initial A).rows ↔ Admissible W := by
  exact initial_rowProduct_eq_admissible

theorem initial_every_selection_consistent (A : DeterministicStrategy m)
    {W : RowMatrix m} (hW : W ∈ rowProduct (initial A).rows) :
    Consistent A (initial A).answers W :=
  (initial A).every_selection_consistent hW

end OracleState

end ZeroOrderBounds
