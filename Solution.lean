import ZeroOrderBounds

/-!
# Comparator solution wrapper for the fixed-horizon lower bound

This repeats the trusted challenge statement and delegates its proof to the
formalization's public endpoint.
-/

open Metric

theorem fixedHorizonLowerBound_strict
    {m T : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (horizon : 1000 * T ≤ m ^ 2)
    (A : ZeroOrderBounds.DeterministicStrategy m) :
    ∃ ys : List ℝ, ∃ W : ZeroOrderBounds.RowMatrix m,
      ys.length = T ∧
      ZeroOrderBounds.Admissible W ∧
      ZeroOrderBounds.hardObjective W 0 = 0 ∧
      ConvexOn ℝ Set.univ (ZeroOrderBounds.hardObjective W) ∧
      LipschitzWith 1 (ZeroOrderBounds.hardObjective W) ∧
      ZeroOrderBounds.Consistent A ys W ∧
      ZeroOrderBounds.hardOptimizer W ∈ ZeroOrderBounds.unitBall m ∧
      IsMinOn (ZeroOrderBounds.hardObjective W) (ZeroOrderBounds.unitBall m)
        (ZeroOrderBounds.hardOptimizer W) ∧
      1 / (200000000 * (m : ℝ) ^ 3) <
        ZeroOrderBounds.hardObjective W
            (A.output ys : ZeroOrderBounds.QuerySpace m) -
          ZeroOrderBounds.hardObjective W (ZeroOrderBounds.hardOptimizer W) := by
  obtain ⟨ys, W, hlen, hW, hconsistent, hoptimizer, hmin, hgap⟩ :=
    ZeroOrderBounds.fixedHorizonLowerBound_strict hm horizon A
  exact ⟨ys, W, hlen, hW, ZeroOrderBounds.hardObjective_zero W,
    ZeroOrderBounds.convexOn_hardObjective W,
    ZeroOrderBounds.hardObjective_lipschitzWith_one W hW,
    hconsistent, hoptimizer, hmin, hgap⟩
