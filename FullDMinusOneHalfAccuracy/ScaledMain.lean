import FullDMinusOneHalfAccuracy.Main
import FullDMinusOneHalfAccuracy.Scaling

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Unconditional radius/Lipschitz lower bound

This module applies the exact transcript transport from `Scaling.lean` to the
unconditional unit-radius theorem in `Main.lean`.  For a domain ball of radius
`R` and an `L`-Lipschitz objective, both the hard gap and the accuracy threshold
are multiplied by `L * R`.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- The unconditional fixed-horizon lower bound on the radius-`R` ball for
`L`-Lipschitz objectives.  The conclusion retains the hard-matrix witness so
that every class, transcript, optimizer, and gap certificate is directly
auditable. -/
theorem scaledFixedHorizonSqrtLowerBound_strict
    {m T : ℕ} [NeZero m] {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (horizon : (T : ℝ) ≤ paperQueryThreshold m)
    (A : RadiusDeterministicStrategy m R) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      scaledHardObjective R L W 0 = 0 ∧
      ConvexOn ℝ Set.univ (scaledHardObjective R L W) ∧
      LipschitzWith ⟨L, hL.le⟩ (scaledHardObjective R L W) ∧
      RadiusConsistent A ys (scaledHardObjective R L W) ∧
      scaledHardOptimizer R W ∈ radiusBall m R ∧
      IsMinOn (scaledHardObjective R L W) (radiusBall m R)
        (scaledHardOptimizer R W) ∧
      (L * R) * sqrtAccuracy m <
        scaledHardObjective R L W (A.output ys : QuerySpace m) -
          scaledHardObjective R L W (scaledHardOptimizer R W) := by
  apply scaledFixedHorizonLowerBound_strict_of_unit hR hL
  intro B
  obtain ⟨ys, W, hlen, hW, _, _, _, hcons, hopt, hmin, hgap⟩ :=
    fixedHorizonSqrtLowerBound_strict
      (by simpa [paperQueryThreshold, paperLog] using horizon) B
  exact ⟨ys, W, hlen, hW, hcons, hopt, hmin, hgap⟩

/-- Monotone form of the scaled endpoint: every accuracy at most the paper's
`L * R / sqrt(d)` threshold is defeated by the same hard family. -/
theorem scaledFixedHorizonLowerBound_strict_of_le_sqrtAccuracy
    {m T : ℕ} [NeZero m] {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hε : ε ≤ (L * R) * sqrtAccuracy m)
    (horizon : (T : ℝ) ≤ paperQueryThreshold m)
    (A : RadiusDeterministicStrategy m R) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      scaledHardObjective R L W 0 = 0 ∧
      ConvexOn ℝ Set.univ (scaledHardObjective R L W) ∧
      LipschitzWith ⟨L, hL.le⟩ (scaledHardObjective R L W) ∧
      RadiusConsistent A ys (scaledHardObjective R L W) ∧
      scaledHardOptimizer R W ∈ radiusBall m R ∧
      IsMinOn (scaledHardObjective R L W) (radiusBall m R)
        (scaledHardOptimizer R W) ∧
      ε <
        scaledHardObjective R L W (A.output ys : QuerySpace m) -
          scaledHardObjective R L W (scaledHardOptimizer R W) := by
  obtain ⟨ys, W, hlen, hW, hzero, hconv, hlip, hcons, hopt, hmin, hgap⟩ :=
    scaledFixedHorizonSqrtLowerBound_strict hR hL horizon A
  exact ⟨ys, W, hlen, hW, hzero, hconv, hlip, hcons, hopt, hmin,
    hε.trans_lt hgap⟩

/-! ## Uniform-success formulation -/

/-- A deterministic radius-`R` strategy succeeds uniformly on the scaled hard
family within additive error `ε` after exactly `T` value queries. -/
def RadiusSucceedsWithin (m T : ℕ) [NeZero m]
    (R L ε : ℝ) : Prop :=
  ∃ A : RadiusDeterministicStrategy m R,
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = T →
      Admissible W →
      RadiusConsistent A ys (scaledHardObjective R L W) →
      scaledHardObjective R L W (A.output ys : QuerySpace m) -
          scaledHardObjective R L W (scaledHardOptimizer R W) ≤ ε

/-- Below the paper horizon, no deterministic radius-`R` strategy succeeds at
the scaled `d⁻¹ᐟ²` accuracy. -/
theorem not_radiusSucceedsWithinSqrt
    {m T : ℕ} [NeZero m] {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (horizon : (T : ℝ) ≤ paperQueryThreshold m) :
    ¬ RadiusSucceedsWithin m T R L ((L * R) * sqrtAccuracy m) := by
  intro hsuccess
  obtain ⟨A, hA⟩ := hsuccess
  obtain ⟨ys, W, hlen, hW, _, _, _, hcons, _, _, hgap⟩ :=
    scaledFixedHorizonSqrtLowerBound_strict hR hL horizon A
  exact (not_lt_of_ge (hA ys W hlen hW hcons)) hgap

/-- The impossibility is monotone in the requested accuracy: it holds for
every `ε` no larger than the scaled paper threshold. -/
theorem not_radiusSucceedsWithin_of_le_sqrtAccuracy
    {m T : ℕ} [NeZero m] {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hε : ε ≤ (L * R) * sqrtAccuracy m)
    (horizon : (T : ℝ) ≤ paperQueryThreshold m) :
    ¬ RadiusSucceedsWithin m T R L ε := by
  intro hsuccess
  obtain ⟨A, hA⟩ := hsuccess
  obtain ⟨ys, W, hlen, hW, _, _, _, hcons, _, _, hgap⟩ :=
    scaledFixedHorizonLowerBound_strict_of_le_sqrtAccuracy
      hR hL hε horizon A
  exact (not_lt_of_ge (hA ys W hlen hW hcons)) hgap

end ZeroOrderBounds.AccuracyImprovement
