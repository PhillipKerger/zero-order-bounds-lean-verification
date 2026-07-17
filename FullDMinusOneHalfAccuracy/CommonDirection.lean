import FullDMinusOneHalfAccuracy.SphericalProjection
import ZeroOrderBounds.OracleState
import Mathlib.Tactic.NormNum

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# A common direction from spherical mean-width bounds

This module contains the finite averaging step that turns one ambient
mean-width lower bound for each good row into a single direction which is
simultaneously useful in aggregate.  It is independent of how the individual
mean-width estimates are proved (Urysohn plus spherical projection in the
paper).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Metric Set

namespace ZeroOrderBounds.AccuracyImprovement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The full directional width averaged against normalized surface measure
on the ambient unit sphere. -/
def sphericalMeanWidth [Nontrivial E] (s : Set E) : ℝ :=
  ∫ θ : UnitSphere E, directionalWidth s (θ : E)
    ∂(sphereProbability E : Measure (UnitSphere E))

/-- The set-level mean-width API used by the common-direction argument is
definitionally the ambient mean width of an intrinsic body. -/
theorem sphericalMeanWidth_carrier_eq_ambientMeanWidth [Nontrivial E]
    (P : IntrinsicBody E) :
    sphericalMeanWidth P.carrier = ambientMeanWidth P :=
  rfl

/-- The integrand defining ambient spherical mean width is continuous. -/
theorem continuous_directionalWidth_on_unitSphere {s : Set E}
    (hs : IsCompact s) :
    Continuous (fun θ : UnitSphere E ↦ directionalWidth s (θ : E)) :=
  (continuous_directionalWidth hs).comp continuous_subtype_val

/-- The integrand defining ambient spherical mean width is integrable. -/
theorem integrable_directionalWidth_on_unitSphere [Nontrivial E]
    {s : Set E} (hs : IsCompact s) :
    Integrable (fun θ : UnitSphere E ↦ directionalWidth s (θ : E))
      (sphereProbability E : Measure (UnitSphere E)) :=
  Continuous.integrable_sphereProbability
    (E := E) (continuous_directionalWidth_on_unitSphere hs)

/-- Integration commutes with a finite sum of compact-set width functions. -/
theorem integral_sum_directionalWidth_on_unitSphere [Nontrivial E]
    {ι : Type*} (G : Finset ι) (s : ι → Set E)
    (hs : ∀ i ∈ G, IsCompact (s i)) :
    (∫ θ : UnitSphere E,
        ∑ i ∈ G, directionalWidth (s i) (θ : E)
      ∂(sphereProbability E : Measure (UnitSphere E))) =
      ∑ i ∈ G, sphericalMeanWidth (s i) := by
  rw [integral_finsetSum]
  · rfl
  · intro i hi
    exact integrable_directionalWidth_on_unitSphere (hs i hi)

/-- A finite family of compact bodies has one direction at which its total
width is at least the sum of its spherical mean widths. -/
theorem exists_sum_sphericalMeanWidth_le_sum_directionalWidth
    [Nontrivial E] {ι : Type*} (G : Finset ι) (s : ι → Set E)
    (hs : ∀ i ∈ G, IsCompact (s i)) :
    ∃ θ : UnitSphere E,
      (∑ i ∈ G, sphericalMeanWidth (s i)) ≤
        ∑ i ∈ G, directionalWidth (s i) (θ : E) := by
  have hcontinuous : Continuous (fun θ : UnitSphere E ↦
      ∑ i ∈ G, directionalWidth (s i) (θ : E)) := by
    apply continuous_finsetSum
    intro i hi
    exact continuous_directionalWidth_on_unitSphere (hs i hi)
  obtain ⟨θ, hθ⟩ := exists_integral_le_sphere_value (E := E) hcontinuous
  refine ⟨θ, ?_⟩
  rw [integral_sum_directionalWidth_on_unitSphere G s hs] at hθ
  exact hθ

/-- If every member of a finite family has mean width at least `c`, one
direction has aggregate width at least `G.card * c`. -/
theorem exists_card_mul_le_sum_directionalWidth_of_le_sphericalMeanWidth
    [Nontrivial E] {ι : Type*} (G : Finset ι) (s : ι → Set E)
    (hs : ∀ i ∈ G, IsCompact (s i)) (c : ℝ)
    (hmean : ∀ i ∈ G, c ≤ sphericalMeanWidth (s i)) :
    ∃ θ : UnitSphere E,
      (G.card : ℝ) * c ≤
        ∑ i ∈ G, directionalWidth (s i) (θ : E) := by
  obtain ⟨θ, hθ⟩ :=
    exists_sum_sphericalMeanWidth_le_sum_directionalWidth G s hs
  refine ⟨θ, ?_⟩
  calc
    (G.card : ℝ) * c = ∑ _i ∈ G, c := by simp
    _ ≤ ∑ i ∈ G, sphericalMeanWidth (s i) := by
      exact Finset.sum_le_sum fun i hi ↦ hmean i hi
    _ ≤ ∑ i ∈ G, directionalWidth (s i) (θ : E) := hθ

/-- Paper-specialized common-direction theorem.  Mean width `tau/2` on at
least half of the rows gives aggregate width `m*tau/4`. -/
theorem exists_common_direction_of_row_meanWidth
    {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (G : Finset (Fin m)) (hcard : m ≤ 2 * G.card)
    (hmean : ∀ i ∈ G,
      tau m / 2 ≤ sphericalMeanWidth (rows i : Set (RowSpace m))) :
    ∃ θ : RowSpace m,
      ‖θ‖ = 1 ∧
      (m : ℝ) * tau m / 4 ≤
        ∑ i ∈ G, directionalWidth (rows i : Set (RowSpace m)) θ := by
  obtain ⟨θ, hθ⟩ :=
    exists_card_mul_le_sum_directionalWidth_of_le_sphericalMeanWidth
      G (fun i ↦ (rows i : Set (RowSpace m)))
      (fun i _hi ↦ (rows i).isCompact) (tau m / 2) hmean
  refine ⟨(θ : RowSpace m), norm_coe_unitSphere (E := RowSpace m) θ, ?_⟩
  have hcardR : (m : ℝ) ≤ 2 * (G.card : ℝ) := by
    exact_mod_cast hcard
  have htau : 0 ≤ tau m :=
    (tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))).le
  calc
    (m : ℝ) * tau m / 4 ≤ (G.card : ℝ) * (tau m / 2) := by
      nlinarith
    _ ≤ ∑ i ∈ G,
        directionalWidth (rows i : Set (RowSpace m)) (θ : RowSpace m) := hθ

end ZeroOrderBounds.AccuracyImprovement
