import ZeroOrderBounds.Statement

/-!
# Trusted Comparator challenge for the fixed-horizon lower bound

The proof placeholder is intentional.  Comparator compares this reviewed
statement with `Solution.fixedHorizonLowerBound_strict` and audits only the
solution's proof dependencies.
-/

open Metric

/-- Trusted statement of the deterministic exact-value fixed-horizon lower bound,
including the objective-class certificates used to interpret the witness. -/
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
  sorry
