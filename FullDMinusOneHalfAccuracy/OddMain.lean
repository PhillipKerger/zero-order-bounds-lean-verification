import FullDMinusOneHalfAccuracy.Main
import FullDMinusOneHalfAccuracy.OddDimension

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Unconditional odd-dimensional fixed-horizon lower bound

The production theorem in `Main` handles dimension `2m`.  This module applies the
projection-and-lift reduction from `OddDimension` to obtain the same fixed-horizon
lower bound in dimension `2m+1`, at the paper's ambient accuracy
`10⁻⁷ / sqrt (2m+1)`.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-- The unconditional odd-dimensional fixed-horizon theorem, including exact
transcript, objective-class, and optimizer certificates. -/
theorem oddFixedHorizonSqrtLowerBound_strict
    {m T : ℕ} [NeZero m]
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 /
        Real.log (Real.exp 1 * (m : ℝ)))
    (A : AmbientDeterministicStrategy (2 * m + 1)) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      oddHardObjective W 0 = 0 ∧
      ConvexOn ℝ Set.univ (oddHardObjective W) ∧
      LipschitzWith 1 (oddHardObjective W) ∧
      AmbientConsistent A ys (oddHardObjective W) ∧
      oddHardOptimizer W ∈ ambientUnitBall (2 * m + 1) ∧
      IsMinOn (oddHardObjective W) (ambientUnitBall (2 * m + 1))
        (oddHardOptimizer W) ∧
      oddSqrtAccuracy m <
        oddHardObjective W
            (A.output ys : AmbientQuerySpace (2 * m + 1)) -
          oddHardObjective W (oddHardOptimizer W) := by
  apply oddFixedHorizonLowerBound_strict_of_even
  intro B
  exact fixedHorizonSqrtLowerBound_strict horizon B

/-! ## Function-class success and impossibility -/

/-- A strategy succeeds uniformly on normalized convex one-Lipschitz objectives
over the standard `d`-dimensional unit ball after exactly `T` value queries.

The optimizer is supplied as part of the universally quantified certificate;
thus objectives without an attained unit-ball minimum do not create a vacuous
extra obligation. -/
def AmbientSucceedsWithin (d T : ℕ) (ε : ℝ) : Prop :=
  ∃ A : AmbientDeterministicStrategy d,
    ∀ (ys : List ℝ) (f : AmbientQuerySpace d → ℝ)
      (xstar : AmbientQuerySpace d),
      ys.length = T →
      f 0 = 0 →
      ConvexOn ℝ Set.univ f →
      LipschitzWith 1 f →
      AmbientConsistent A ys f →
      xstar ∈ ambientUnitBall d →
      IsMinOn f (ambientUnitBall d) xstar →
      f (A.output ys : AmbientQuerySpace d) - f xstar ≤ ε

/-- At the same horizon as the even-dimensional theorem, no deterministic
strategy succeeds for all normalized convex one-Lipschitz objectives in
dimension `2m+1` at ambient accuracy `10⁻⁷ / sqrt (2m+1)`. -/
theorem not_ambientSucceedsWithin_oddSqrtAccuracy
    {m T : ℕ} [NeZero m]
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 /
        Real.log (Real.exp 1 * (m : ℝ))) :
    ¬ AmbientSucceedsWithin (2 * m + 1) T (oddSqrtAccuracy m) := by
  rintro ⟨A, hA⟩
  obtain ⟨ys, W, hlen, _hW, hzero, hconvex, hlipschitz,
    hconsistent, hoptimizer, hmin, hgap⟩ :=
      oddFixedHorizonSqrtLowerBound_strict horizon A
  have hsuccess := hA ys (oddHardObjective W) (oddHardOptimizer W)
    hlen hzero hconvex hlipschitz hconsistent hoptimizer hmin
  exact (not_le_of_gt hgap) hsuccess

/-- Every integer horizon at most the paper's floored even-core budget is
impossible in the lifted odd dimension. -/
theorem not_ambientSucceedsWithin_oddSqrtAccuracy_of_le_paperQueryBudget
    {m T : ℕ} [NeZero m] (hT : T ≤ paperQueryBudget m) :
    ¬ AmbientSucceedsWithin (2 * m + 1) T (oddSqrtAccuracy m) := by
  apply not_ambientSucceedsWithin_oddSqrtAccuracy
  simpa only [paperLog] using
    horizon_of_le_paperQueryBudget
      (Nat.pos_of_ne_zero (NeZero.ne m)) hT

/-! ## Explicit odd-dimensional quadratic-over-logarithmic rate -/

/-- The odd-dimensional rate with a clean `log(d+1)` denominator is bounded by
the already verified even-core rate.  The factor `1800/800 = (3/2)²` absorbs
the worst case `2m+1 ≤ (3/2)(2m)`, attained at `m=1`. -/
theorem odd_dimension_log_succ_rate_le_even_dimension_rate
    {m : ℕ} (hm : 0 < m) :
    ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
        (1800 * Real.log ((2 * m + 2 : ℕ) : ℝ)) ≤
      (2 * (m : ℝ)) ^ 2 /
        (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hargOdd : (1 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < 2 * m + 1)
  have hargOddPos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) :=
    zero_lt_one.trans hargOdd
  have hlogOdd : 0 < Real.log ((2 * m + 1 : ℕ) : ℝ) :=
    Real.log_pos hargOdd
  have hargMono : ((2 * m + 1 : ℕ) : ℝ) ≤
      ((2 * m + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * m + 2)
  have hlogMono : Real.log ((2 * m + 1 : ℕ) : ℝ) ≤
      Real.log ((2 * m + 2 : ℕ) : ℝ) :=
    Real.log_le_log hargOddPos hargMono
  have hfirst :
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
          (1800 * Real.log ((2 * m + 2 : ℕ) : ℝ)) ≤
        ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
          (1800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) := by
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (mul_pos (by norm_num) hlogOdd)
      (mul_le_mul_of_nonneg_left hlogMono (by norm_num))
  have hfactor :
      0 ≤ (5 * (m : ℝ) + 1) * ((m : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hnumerator :
      800 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤
        1800 * (2 * (m : ℝ)) ^ 2 := by
    push_cast
    nlinarith
  have hsecond :
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
          (1800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) ≤
        (2 * (m : ℝ)) ^ 2 /
          (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) hlogOdd)
      (mul_pos (by norm_num) hlogOdd)).2
    calc
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 *
          (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) =
          (800 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) *
            Real.log ((2 * m + 1 : ℕ) : ℝ) := by ring
      _ ≤ (1800 * (2 * (m : ℝ)) ^ 2) *
            Real.log ((2 * m + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hnumerator hlogOdd.le
      _ = (2 * (m : ℝ)) ^ 2 *
          (1800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) := by ring
  exact hfirst.trans hsecond

/-- In odd ambient dimension `d=2m+1`, the successor of the ruled-out budget
is strictly larger than `d² / (1800 log(d+1))`. -/
theorem paperQueryBudget_succ_gt_odd_dimension_log_succ_rate
    {m : ℕ} (hm : 0 < m) :
    ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
        (1800 * Real.log ((2 * m + 2 : ℕ) : ℝ)) <
      ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact (odd_dimension_log_succ_rate_le_even_dimension_rate hm).trans_lt
    (paperQueryBudget_succ_gt_even_dimension_log_succ_rate hm)

/-- Audit-facing odd-dimensional complexity statement: the canonical floored
budget is impossible, while its successor exceeds an explicit
quadratic-over-logarithmic function of the ambient dimension. -/
theorem not_ambientPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate
    {m : ℕ} [NeZero m] :
    (¬ AmbientSucceedsWithin (2 * m + 1) (paperQueryBudget m)
        (oddSqrtAccuracy m)) ∧
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
          (1800 * Real.log ((2 * m + 2 : ℕ) : ℝ)) <
        ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact ⟨
    not_ambientSucceedsWithin_oddSqrtAccuracy_of_le_paperQueryBudget le_rfl,
    paperQueryBudget_succ_gt_odd_dimension_log_succ_rate
      (Nat.pos_of_ne_zero (NeZero.ne m))⟩

end ZeroOrderBounds.AccuracyImprovement
