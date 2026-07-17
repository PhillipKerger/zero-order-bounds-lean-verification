import FullDMinusOneHalfAccuracy.BrunnMinkowskiProduct

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Brunn--Minkowski in every standard Euclidean dimension

This module closes the dimension induction.  The coordinate map
`euclideanSuccEquivLpProduct` is an orthogonal, hence volume-preserving,
identification

`EuclideanSpace ℝ (Fin (n + 1)) ≃ WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))`.

The one-dimensional theorem is the interval computation in
`BrunnMinkowski.lean`; the successor step is
`brunnMinkowskiAt_withLpProduct_of_lower_dim`.  The final theorem has exactly
the dimension-uniform interface consumed by `MainBridge.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

/-- The canonical orthogonal identification of one-dimensional Euclidean
space with `ℝ`. -/
def euclideanOneEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finCongr (Module.finrank_self ℝ).symm)).trans
      (stdOrthonormalBasis ℝ ℝ).repr.symm

/-- Split the first coordinate from standard `(n+1)`-dimensional Euclidean
space.  Every component of the definition is a linear isometry equivalence,
so the composite preserves the canonical volume measure. -/
def euclideanSuccEquivLpProduct (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finCongr (Nat.add_comm n 1)).trans
      (@finSumFinEquiv 1 n).symm)).trans <|
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)).trans <|
  LinearIsometryEquiv.withLpProdCongr 2
    euclideanOneEquivReal
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))

/-- The one-dimensional base case in standard Euclidean coordinates. -/
theorem brunnMinkowskiAt_euclidean_one
    (t : ℝ) (K L : ConvexBody (EuclideanSpace ℝ (Fin 1)))
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K L := by
  let e := euclideanOneEquivReal
  have hReal : BrunnMinkowskiAt t
      (continuousLinearEquivImage e.toContinuousLinearEquiv K)
      (continuousLinearEquivImage e.toContinuousLinearEquiv L) :=
    brunnMinkowskiAt_real _ _ ht₀ ht₁
  exact hReal.of_map_continuousLinearEquiv e.toContinuousLinearEquiv
    e.measurePreserving

/-- Full Brunn--Minkowski in every positive standard Euclidean dimension.
This is the public geometric theorem used by the final optimization bridge. -/
theorem brunnMinkowskiAt_euclidean
    (n : ℕ) (hn : 0 < n)
    (t : ℝ) (K L : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K L := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases n with
      | zero => omega
      | succ k =>
          by_cases hk : k = 0
          · subst k
            exact brunnMinkowskiAt_euclidean_one t K L ht₀ ht₁
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
            have hLower : ∀ (s : ℝ)
                (A B : ConvexBody (EuclideanSpace ℝ (Fin k))),
                0 ≤ s → s ≤ 1 → BrunnMinkowskiAt s A B := by
              intro s A B hs₀ hs₁
              exact ih k (Nat.lt_succ_self k) hkpos s A B hs₀ hs₁
            let e := euclideanSuccEquivLpProduct k
            have hProduct : BrunnMinkowskiAt t
                (continuousLinearEquivImage e.toContinuousLinearEquiv K)
                (continuousLinearEquivImage e.toContinuousLinearEquiv L) :=
              brunnMinkowskiAt_withLpProduct_of_lower_dim
                hLower (by simpa using hk) _ _ ht₀ ht₁
            exact hProduct.of_map_continuousLinearEquiv
              e.toContinuousLinearEquiv e.measurePreserving

/-- Curried form matching the hypothesis of
`fixedHorizonSqrtLowerBound_strict_of_euclidean_brunnMinkowski` exactly. -/
theorem euclidean_brunnMinkowski_family :
    ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ) (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
        0 ≤ t → t ≤ 1 → BrunnMinkowskiAt t K L := by
  intro n hn t K L ht₀ ht₁
  exact brunnMinkowskiAt_euclidean n hn t K L ht₀ ht₁

end ZeroOrderBounds.AccuracyImprovement
