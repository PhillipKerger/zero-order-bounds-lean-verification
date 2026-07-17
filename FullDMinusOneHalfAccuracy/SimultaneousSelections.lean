import ZeroOrderBounds.OracleState
import FullDMinusOneHalfAccuracy.DirectionalWidth
import Mathlib.Tactic.Module

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Simultaneous extremal selections from all good row bodies

For each good row we choose a maximizer and minimizer of a common linear
functional.  Outside the good-row finset the two matrices use the same point.
The construction is deliberately isolated from the later barycentric
estimates: this file contains only compactness, finite choice, and Cartesian
product membership.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds.AccuracyImprovement

/-- Two row selections which realize every directional width on `G` and agree
on its complement.  The maximum/minimum clauses make the witness construction
directly auditable; `width_eq` is the equation used downstream. -/
structure SimultaneousWidthSelection {m : ℕ}
    (rows : Fin m → RowBody m) (G : Finset (Fin m)) (θ : RowSpace m) where
  plus : RowMatrix m
  minus : RowMatrix m
  plus_mem : plus ∈ rowProduct rows
  minus_mem : minus ∈ rowProduct rows
  agree_of_not_mem : ∀ i, i ∉ G → plus i = minus i
  plus_max : ∀ i ∈ G, ∀ w ∈ rows i,
    inner ℝ θ w ≤ inner ℝ θ (plus i)
  minus_min : ∀ i ∈ G, ∀ w ∈ rows i,
    inner ℝ θ (minus i) ≤ inner ℝ θ w
  width_eq : ∀ i ∈ G,
    directionalWidth (rows i : Set (RowSpace m)) θ =
      inner ℝ θ (plus i - minus i)

/-- Compactness of every row body provides a simultaneous extremal selection.
Only good rows use distinct extrema; the minus selection is copied from plus
outside `G`. -/
theorem exists_simultaneousWidthSelection {m : ℕ}
    (rows : Fin m → RowBody m) (G : Finset (Fin m)) (θ : RowSpace m) :
    Nonempty (SimultaneousWidthSelection rows G θ) := by
  classical
  have hextrema : ∀ i : Fin m,
      ∃ p ∈ (rows i : Set (RowSpace m)),
        ∃ q ∈ (rows i : Set (RowSpace m)),
          (∀ w ∈ (rows i : Set (RowSpace m)),
              inner ℝ θ w ≤ inner ℝ θ p) ∧
          (∀ w ∈ (rows i : Set (RowSpace m)),
              inner ℝ θ q ≤ inner ℝ θ w) ∧
          directionalWidth (rows i : Set (RowSpace m)) θ =
            inner ℝ θ p - inner ℝ θ q := by
    intro i
    exact IsCompact.exists_directionalWidth_eq
      (rows i).isCompact (rows i).nonempty θ
  choose p hp q hq hpmax hqmin hwidth using hextrema
  let Wplus : RowMatrix m := p
  let Wminus : RowMatrix m := fun i ↦ if i ∈ G then q i else p i
  refine ⟨{
    plus := Wplus
    minus := Wminus
    plus_mem := ?_
    minus_mem := ?_
    agree_of_not_mem := ?_
    plus_max := ?_
    minus_min := ?_
    width_eq := ?_ }⟩
  · intro i
    exact hp i
  · intro i
    by_cases hi : i ∈ G
    · simpa [Wminus, hi] using hq i
    · simpa [Wminus, hi] using hp i
  · intro i hi
    simp [Wplus, Wminus, hi]
  · intro i _hi w hw
    simpa [Wplus] using hpmax i w hw
  · intro i hi w hw
    simpa [Wminus, hi] using hqmin i w hw
  · intro i hi
    simpa [Wplus, Wminus, hi, inner_sub_right] using hwidth i

/-- Unbundled existential form of `exists_simultaneousWidthSelection`. -/
theorem exists_simultaneous_extremal_matrices {m : ℕ}
    (rows : Fin m → RowBody m) (G : Finset (Fin m)) (θ : RowSpace m) :
    ∃ Wplus Wminus : RowMatrix m,
      Wplus ∈ rowProduct rows ∧
      Wminus ∈ rowProduct rows ∧
      (∀ i, i ∉ G → Wplus i = Wminus i) ∧
      (∀ i ∈ G, ∀ w ∈ rows i,
        inner ℝ θ w ≤ inner ℝ θ (Wplus i)) ∧
      (∀ i ∈ G, ∀ w ∈ rows i,
        inner ℝ θ (Wminus i) ≤ inner ℝ θ w) ∧
      (∀ i ∈ G,
        directionalWidth (rows i : Set (RowSpace m)) θ =
          inner ℝ θ (Wplus i - Wminus i)) := by
  let S := Classical.choice (exists_simultaneousWidthSelection rows G θ)
  exact ⟨S.plus, S.minus, S.plus_mem, S.minus_mem,
    S.agree_of_not_mem, S.plus_max, S.minus_min, S.width_eq⟩

/-- The sum of all row displacements equals the sum of widths over the good
rows.  Displacements outside `G` vanish by construction. -/
theorem sum_inner_row_sub_eq_sum_directionalWidth
    {m : ℕ} {rows : Fin m → RowBody m} {G : Finset (Fin m)}
    {θ : RowSpace m} (S : SimultaneousWidthSelection rows G θ) :
    ∑ i, inner ℝ θ (S.plus i - S.minus i) =
      ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ := by
  symm
  calc
    ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ =
        ∑ i ∈ G, inner ℝ θ (S.plus i - S.minus i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [S.width_eq i hi]
    _ = ∑ i, inner ℝ θ (S.plus i - S.minus i) := by
      apply Finset.sum_subset (Finset.subset_univ G)
      intro i _hi hiG
      simp [S.agree_of_not_mem i hiG]

end ZeroOrderBounds.AccuracyImprovement
