import FullDMinusOneHalfAccuracy.Solution
import FullDMinusOneHalfAccuracy.OddMain
import FullDMinusOneHalfAccuracy.ScaledMain
import FullDMinusOneHalfAccuracy.UrysohnMain
import FullDMinusOneHalfAccuracy.PaperStopping

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Axiom audit for the improved-accuracy public endpoints

This module is compiled independently at trust level zero.  The guarded messages
below pin the complete axiom set of the geometric roots, the production theorem
and its Comparator wrapper, and the normalized, odd-dimensional, and scaled
complexity endpoints.
-/

/--
info: 'ZeroOrderBounds.AccuracyImprovement.fixedHorizonSqrtLowerBound_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.AccuracyImprovement.fixedHorizonSqrtLowerBound_strict

/--
info: 'fixedHorizonSqrtLowerBound_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedHorizonSqrtLowerBound_strict

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_succeedsWithinSqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.AccuracyImprovement.not_succeedsWithinSqrt

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_atMostPaperQueryBudgetSucceedsWithinSqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.AccuracyImprovement.not_atMostPaperQueryBudgetSucceedsWithinSqrt

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_atMostPaperQueryBudgetSucceedsWithinSqrt_and_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ZeroOrderBounds.AccuracyImprovement.not_atMostPaperQueryBudgetSucceedsWithinSqrt_and_rate

namespace ZeroOrderBounds.AccuracyImprovement

/-! ## Geometric roots -/

/--
info: 'ZeroOrderBounds.AccuracyImprovement.euclidean_brunnMinkowski_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms euclidean_brunnMinkowski_family

/--
info: 'ZeroOrderBounds.AccuracyImprovement.two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  two_mul_intrinsicVolumeRadius_le_intrinsicMeanWidth_unconditional

/--
info: 'ZeroOrderBounds.AccuracyImprovement.tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  tau_le_positiveIntrinsicMeanWidth_of_normalizedVolumeRadius_unconditional

/-! ## Odd-dimensional and scaled public endpoints -/

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_ambientPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  not_ambientPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate

/--
info: 'ZeroOrderBounds.AccuracyImprovement.scaledFixedHorizonSqrtLowerBound_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  scaledFixedHorizonSqrtLowerBound_strict

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_radiusSucceedsWithinSqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms not_radiusSucceedsWithinSqrt

/-! ## Transcript-dependent paper endpoints -/

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_ambientAtMostPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  not_ambientAtMostPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate

/--
info: 'ZeroOrderBounds.AccuracyImprovement.not_radiusAtMostPaperQueryBudgetSucceedsWithinSqrt_and_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  not_radiusAtMostPaperQueryBudgetSucceedsWithinSqrt_and_rate

end ZeroOrderBounds.AccuracyImprovement
