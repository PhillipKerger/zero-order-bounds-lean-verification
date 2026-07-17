import FullDMinusOneHalfAccuracy.Statement

/-!
# Trusted Comparator challenge for the `d⁻¹ᐟ²` lower bound

The proof placeholder is intentional.  Comparator compares this reviewed
statement with
`FullDMinusOneHalfAccuracy.Solution.fixedHorizonSqrtLowerBound_strict`
and audits only the solution's proof dependencies.
-/

open Metric

/-- Trusted fixed-horizon statement of the paper's improved-accuracy lower
bound, including all objective-class and transcript certificates. -/
theorem fixedHorizonSqrtLowerBound_strict
    {m T : ℕ} [NeZero m]
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 /
        Real.log (Real.exp 1 * (m : ℝ)))
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
      ZeroOrderBounds.AccuracyImprovement.sqrtAccuracy m <
        ZeroOrderBounds.hardObjective W
            (A.output ys : ZeroOrderBounds.QuerySpace m) -
          ZeroOrderBounds.hardObjective W
            (ZeroOrderBounds.hardOptimizer W) := by
  sorry
