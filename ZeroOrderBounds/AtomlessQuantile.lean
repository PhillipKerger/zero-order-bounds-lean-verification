import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Exact quantiles for atomless probability measures

The resisting oracle needs exact, rather than approximate, cap volumes.  This
module isolates the one-dimensional measure-theoretic fact behind that choice.
For an atomless probability measure on `ℝ`, its cumulative distribution
function is continuous: right-continuity is part of mathlib's bundled
`StieltjesFunction`, while atomlessness removes every possible left jump.
The intermediate value theorem then gives exact upper-tail quantiles.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace ZeroOrderBounds

/-- The cumulative distribution function of an atomless probability measure is continuous. -/
theorem continuous_cdf_of_nullSingleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim,
    (cdf μ).rightLim_eq]
  apply le_antisymm
  · exact (cdf μ).mono.leftLim_le le_rfl
  · have hs : (cdf μ).measure {x} = 0 := by
      rw [measure_cdf]
      simp
    rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hs
    linarith

/-- Every value strictly between zero and one is attained by an atomless CDF. -/
theorem exists_cdf_eq_of_nullSingleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x, cdf μ x = u := by
  have hlow : ∃ x, cdf μ x < u := by
    have he : ∀ᶠ x in atBot, cdf μ x < u :=
      (tendsto_order.1 (tendsto_cdf_atBot μ)).2 _ hu0
    exact he.exists
  have hhigh : ∃ x, u < cdf μ x := by
    have he : ∀ᶠ x in atTop, u < cdf μ x :=
      (tendsto_order.1 (tendsto_cdf_atTop μ)).1 _ hu1
    exact he.exists
  obtain ⟨a, ha⟩ := hlow
  obtain ⟨b, hb⟩ := hhigh
  have hab : a ≤ b := by
    by_contra hba
    have hmono := (cdf μ).mono (le_of_not_ge hba)
    linarith
  have hu : u ∈ Icc (cdf μ a) (cdf μ b) := ⟨ha.le, hb.le⟩
  exact intermediate_value_univ a b (continuous_cdf_of_nullSingleton μ) hu

/-- An atomless probability measure has an exact upper quantile of any mass in `(0,1)`,
stated using real-valued measure. -/
theorem exists_measureReal_Ici_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ x, μ.real (Ici x) = α := by
  obtain ⟨x, hx⟩ :=
    exists_cdf_eq_of_nullSingleton μ (u := 1 - α) (by linarith) (by linarith)
  refine ⟨x, ?_⟩
  calc
    μ.real (Ici x) = μ.real (Ioi x) := by
      exact measureReal_congr Ioi_ae_eq_Ici.symm
    _ = μ.real (Iic x)ᶜ := by rw [compl_Iic]
    _ = μ.real Set.univ - μ.real (Iic x) :=
      measureReal_compl measurableSet_Iic
    _ = 1 - cdf μ x := by rw [probReal_univ, cdf_eq_real]
    _ = α := by rw [hx]; ring

/-- ENNReal form of `exists_measureReal_Ici_eq`. -/
theorem exists_measure_Ici_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ x, μ (Ici x) = ENNReal.ofReal α := by
  obtain ⟨x, hx⟩ := exists_measureReal_Ici_eq μ hα0 hα1
  refine ⟨x, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
  rw [← measureReal_def, hx, ENNReal.toReal_ofReal hα0.le]

/-- Exact upper quantiles for a finite measure pushed forward by a measurable real-valued map.
The fiber-null assumption is precisely the atomlessness condition needed by the CDF argument. -/
theorem exists_map_Ici_measure_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hμ0 : μ Set.univ ≠ 0) (hfiber : ∀ y, μ (f ⁻¹' {y}) = 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ r, μ (f ⁻¹' Ici r) = ENNReal.ofReal α * μ Set.univ := by
  let ν : Measure ℝ := (μ Set.univ)⁻¹ • μ.map f
  letI : IsProbabilityMeasure ν :=
    ⟨by
      change ((μ Set.univ)⁻¹ • μ.map f) Set.univ = 1
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf MeasurableSet.univ,
        preimage_univ]
      exact ENNReal.inv_mul_cancel hμ0 (measure_ne_top μ Set.univ)⟩
  letI : NullSingletonClass ν :=
    ⟨fun y ↦ by
      change ((μ Set.univ)⁻¹ • μ.map f) {y} = 0
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf (measurableSet_singleton y),
        hfiber y, mul_zero]⟩
  obtain ⟨r, hr⟩ := exists_measure_Ici_eq ν hα0 hα1
  refine ⟨r, ?_⟩
  change (μ Set.univ)⁻¹ * (μ.map f) (Ici r) = ENNReal.ofReal α at hr
  rw [Measure.map_apply hf measurableSet_Ici] at hr
  have hμtop : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  calc
    μ (f ⁻¹' Ici r) = μ Set.univ * ((μ Set.univ)⁻¹ * μ (f ⁻¹' Ici r)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hμ0 hμtop, one_mul]
    _ = μ Set.univ * ENNReal.ofReal α := by rw [hr]
    _ = ENNReal.ofReal α * μ Set.univ := mul_comm _ _

end ZeroOrderBounds
