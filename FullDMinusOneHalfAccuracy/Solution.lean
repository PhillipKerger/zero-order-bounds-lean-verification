import FullDMinusOneHalfAccuracy.Main

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Comparator solution wrapper for the `d⁻¹ᐟ²` lower bound

This declaration repeats the trusted statement in
`Challenge-full-d-1-2-accuracy.lean` verbatim and delegates the proof to the
formalization's unconditional public endpoint.  Keeping the wrapper free of
intermediate lemmas gives Comparator a narrow, human-auditable boundary.
-/

open Metric

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
  exact
    ZeroOrderBounds.AccuracyImprovement.fixedHorizonSqrtLowerBound_strict
      horizon A
