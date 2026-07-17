import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.Matrix

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Haar probability on a finite-dimensional orthogonal group

Mathlib supplies Haar measure for a locally compact topological group, but it
does not currently install compactness or continuity of inversion for its
matrix model of the orthogonal group.  This file supplies those missing
instances for finite real matrices and packages Haar measure normalized on the
whole orthogonal group.

This is the rotation parameter space used by the Urysohn development.
-/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix

namespace ZeroOrderBounds.AccuracyImprovement

universe u

variable (n : Type u) [Fintype n] [DecidableEq n]

/-- Inversion on the matrix orthogonal group is continuous because it is
matrix transpose (the real specialization of star-transpose). -/
instance orthogonalGroupContinuousInv :
    ContinuousInv (Matrix.orthogonalGroup n ℝ) where
  continuous_inv := by
    apply Continuous.subtype_mk
      (continuous_star.comp continuous_subtype_val)

instance orthogonalGroupIsTopologicalGroup :
    IsTopologicalGroup (Matrix.orthogonalGroup n ℝ) where

/-- The real orthogonal group is compact: it is a closed subset of the box of
matrices whose entries lie in `[-1,1]`. -/
theorem isCompact_orthogonalGroup :
    IsCompact (Matrix.orthogonalGroup n ℝ :
      Set (Matrix n n ℝ)) := by
  have hclosed : IsClosed (Matrix.orthogonalGroup n ℝ :
      Set (Matrix n n ℝ)) := by
    rw [show (Matrix.orthogonalGroup n ℝ : Set (Matrix n n ℝ)) =
        {A | A * star A = 1} by
      ext A
      exact Matrix.mem_unitaryGroup_iff]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have hsubset : (Matrix.orthogonalGroup n ℝ : Set (Matrix n n ℝ)) ⊆
      (Set.Icc (-1 : ℝ) 1).matrix := by
    intro A hA
    rw [Set.mem_matrix]
    intro i j
    have hij := entry_norm_bound_of_unitary hA i j
    simpa [Real.norm_eq_abs, abs_le] using hij
  exact (isCompact_Icc.matrix).of_isClosed_subset hclosed hsubset

instance orthogonalGroupCompactSpace :
    CompactSpace (Matrix.orthogonalGroup n ℝ) :=
  isCompact_iff_compactSpace.mp (isCompact_orthogonalGroup n)

instance orthogonalGroupLocallyCompactSpace :
    LocallyCompactSpace (Matrix.orthogonalGroup n ℝ) :=
  inferInstance

/-- The canonical Borel measurable structure on the orthogonal group. -/
local instance orthogonalGroupMeasurableSpace :
    MeasurableSpace (Matrix.orthogonalGroup n ℝ) :=
  borel (Matrix.orthogonalGroup n ℝ)

local instance orthogonalGroupBorelSpace :
    BorelSpace (Matrix.orthogonalGroup n ℝ) := ⟨rfl⟩

/-- The whole compact orthogonal group, bundled as the positive compact used
to normalize Haar measure. -/
def orthogonalPositiveCompact :
    TopologicalSpace.PositiveCompacts (Matrix.orthogonalGroup n ℝ) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

/-- Haar probability on the finite-dimensional orthogonal group. -/
def orthogonalHaarProbability :
    ProbabilityMeasure (Matrix.orthogonalGroup n ℝ) :=
  ⟨Measure.haarMeasure (orthogonalPositiveCompact n), ⟨by
    change Measure.haarMeasure (orthogonalPositiveCompact n)
      ((orthogonalPositiveCompact n :
        TopologicalSpace.PositiveCompacts
          (Matrix.orthogonalGroup n ℝ)) :
        Set (Matrix.orthogonalGroup n ℝ)) = 1
    exact Measure.haarMeasure_self⟩⟩

instance : IsProbabilityMeasure
    (orthogonalHaarProbability n :
      Measure (Matrix.orthogonalGroup n ℝ)) := inferInstance

instance : Measure.IsMulLeftInvariant
    (orthogonalHaarProbability n :
      Measure (Matrix.orthogonalGroup n ℝ)) := by
  change Measure.IsMulLeftInvariant
    (Measure.haarMeasure (orthogonalPositiveCompact n))
  infer_instance

end ZeroOrderBounds.AccuracyImprovement
