import FullDMinusOneHalfAccuracy.BorellBrascampLiebAlgebra
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.ProjIcc

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Monotone transport for Brunn--Minkowski slice densities

This file develops the one-dimensional analytic part of the standard
induction proof of Brunn--Minkowski.  A positive continuous density on a
compact interval has a strictly increasing cumulative distribution
function.  Its inverse quantile is differentiable in the open unit interval,
with derivative the reciprocal of the density.

The eventual application takes the densities to be volumes of hyperplane
slices.  Their `(d-1)`-st roots are concave, hence the densities are
continuous and positive in the interior of their projection intervals.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace ZeroOrderBounds.AccuracyImprovement

/-- The cumulative integral of `f`, starting from `a`. -/
def cumulativeIntegral (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in a..x, f u

@[simp]
theorem cumulativeIntegral_left (a : ℝ) (f : ℝ → ℝ) :
    cumulativeIntegral a f a = 0 := by
  simp [cumulativeIntegral]

theorem cumulativeIntegral_right {a b : ℝ} {f : ℝ → ℝ}
    (hnorm : ∫ u in a..b, f u = 1) :
    cumulativeIntegral a f b = 1 := by
  simpa [cumulativeIntegral] using hnorm

theorem continuous_cumulativeIntegral (a : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    Continuous (cumulativeIntegral a f) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hf.integral_hasStrictDerivAt a x).hasDerivAt.continuousAt

theorem hasStrictDerivAt_cumulativeIntegral (a x : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    HasStrictDerivAt (cumulativeIntegral a f) (f x) x :=
  hf.integral_hasStrictDerivAt a x

/-- The difference of two cumulative values is the integral over the
intervening interval. -/
theorem cumulativeIntegral_sub {a x y : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) :
    cumulativeIntegral a f y - cumulativeIntegral a f x =
      ∫ u in x..y, f u := by
  simp only [cumulativeIntegral]
  exact intervalIntegral.integral_interval_sub_left
    (hf.intervalIntegrable a y) (hf.intervalIntegrable a x)

/-- A continuous density which is positive in the interior of `[a,b]` has
a strictly increasing cumulative integral on that interval. -/
theorem strictMonoOn_cumulativeIntegral {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (cumulativeIntegral a f) (Icc a b) := by
  intro x hx y hy hxy
  rw [← sub_pos, cumulativeIntegral_sub hf]
  apply intervalIntegral.integral_pos hxy hf.continuousOn
  · intro z hz
    exact hfnonneg z ⟨hx.1.trans hz.1.le, hz.2.trans hy.2⟩
  · refine ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact hfpos ((x + y) / 2) ⟨by linarith [hx.1], by linarith [hy.2]⟩

/-- The image of a normalized cumulative integral is the unit interval. -/
theorem cumulativeIntegral_image_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    cumulativeIntegral a f '' Icc a b = Icc 0 1 := by
  rw [(continuous_cumulativeIntegral a hf).continuousOn.image_Icc_of_monotoneOn
    hab.le (strictMonoOn_cumulativeIntegral hab hf hfnonneg hfpos).monotoneOn]
  simp [cumulativeIntegral, hnorm]

/-- A normalized positive density identifies its support interval with the
unit interval via its cumulative integral. -/
noncomputable def cumulativeOrderIso {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    Icc a b ≃o Icc (0 : ℝ) 1 :=
  (strictMonoOn_cumulativeIntegral hab hf hfnonneg hfpos).orderIso
      (cumulativeIntegral a f) (Icc a b) |>.trans
    (OrderIso.setCongr _ _
      (cumulativeIntegral_image_Icc hab hf hfnonneg hfpos hnorm))

@[simp]
theorem cumulativeOrderIso_apply_coe {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) (x : Icc a b) :
    ((cumulativeOrderIso hab hf hfnonneg hfpos hnorm x : Icc (0 : ℝ) 1) : ℝ) =
      cumulativeIntegral a f x :=
  rfl

/-- The quantile of a normalized density, extended constantly outside the
unit interval. -/
noncomputable def densityQuantile {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) : ℝ → ℝ :=
  Subtype.val ∘
    IccExtend (zero_le_one' ℝ)
      (cumulativeOrderIso hab hf hfnonneg hfpos hnorm).symm

theorem densityQuantile_mem_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) (u : ℝ) :
    densityQuantile hab hf hfnonneg hfpos hnorm u ∈ Icc a b :=
  Subtype.coe_prop _

theorem continuous_densityQuantile {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    Continuous (densityQuantile hab hf hfnonneg hfpos hnorm) :=
  continuous_subtype_val.comp
    (cumulativeOrderIso hab hf hfnonneg hfpos hnorm).symm.continuous.Icc_extend'

/-- The cumulative distribution evaluated at its quantile is the identity
on the unit interval. -/
theorem cumulativeIntegral_densityQuantile {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    cumulativeIntegral a f (densityQuantile hab hf hfnonneg hfpos hnorm u) = u := by
  let e := cumulativeOrderIso hab hf hfnonneg hfpos hnorm
  have he := e.apply_symm_apply ⟨u, hu⟩
  apply Subtype.ext_iff.mp at he
  simpa only [e, densityQuantile, Function.comp_apply,
    IccExtend_of_mem (zero_le_one' ℝ) _ hu,
    cumulativeOrderIso_apply_coe] using he

/-- Quantiles invert the cumulative distribution on the support interval. -/
theorem densityQuantile_cumulativeIntegral {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) {x : ℝ} (hx : x ∈ Icc a b) :
    densityQuantile hab hf hfnonneg hfpos hnorm (cumulativeIntegral a f x) = x := by
  let e := cumulativeOrderIso hab hf hfnonneg hfpos hnorm
  have hc : cumulativeIntegral a f x ∈ Icc (0 : ℝ) 1 := by
    simpa only [e, cumulativeOrderIso_apply_coe] using (e ⟨x, hx⟩).property
  rw [densityQuantile, Function.comp_apply,
    IccExtend_of_mem (zero_le_one' ℝ) _ hc]
  change ↑(e.symm ⟨cumulativeIntegral a f x, hc⟩) = x
  have harg : (⟨cumulativeIntegral a f x, hc⟩ : Icc (0 : ℝ) 1) = e ⟨x, hx⟩ := by
    ext
    rfl
  rw [harg, e.symm_apply_apply]

@[simp]
theorem densityQuantile_zero {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    densityQuantile hab hf hfnonneg hfpos hnorm 0 = a := by
  simpa only [cumulativeIntegral_left] using
    (densityQuantile_cumulativeIntegral hab hf hfnonneg hfpos hnorm
      (x := a) ⟨le_rfl, hab.le⟩)

@[simp]
theorem densityQuantile_one {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    densityQuantile hab hf hfnonneg hfpos hnorm 1 = b := by
  simpa only [cumulativeIntegral_right hnorm] using
    (densityQuantile_cumulativeIntegral hab hf hfnonneg hfpos hnorm
      (x := b) ⟨hab.le, le_rfl⟩)

/-- Interior quantiles lie in the interior of the support interval. -/
theorem densityQuantile_mem_Ioo {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    densityQuantile hab hf hfnonneg hfpos hnorm u ∈ Ioo a b := by
  have hq := densityQuantile_mem_Icc hab hf hfnonneg hfpos hnorm u
  have hinv := cumulativeIntegral_densityQuantile hab hf hfnonneg hfpos hnorm
    ⟨hu.1.le, hu.2.le⟩
  constructor
  · exact lt_of_le_of_ne hq.1 fun hqa ↦ by
      rw [← hqa, cumulativeIntegral_left] at hinv
      exact hu.1.ne' hinv.symm
  · exact lt_of_le_of_ne hq.2 fun hqb ↦ by
      rw [hqb, cumulativeIntegral_right hnorm] at hinv
      exact hu.2.ne hinv.symm

/-- The derivative of an interior quantile is the reciprocal density. -/
theorem hasDerivAt_densityQuantile {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (densityQuantile hab hf hfnonneg hfpos hnorm)
      (f (densityQuantile hab hf hfnonneg hfpos hnorm u))⁻¹ u := by
  apply HasDerivAt.of_local_left_inverse
    (continuous_densityQuantile hab hf hfnonneg hfpos hnorm).continuousAt
    (hasStrictDerivAt_cumulativeIntegral a
      (densityQuantile hab hf hfnonneg hfpos hnorm u) hf).hasDerivAt
    (hfpos _ (densityQuantile_mem_Ioo hab hf hfnonneg hfpos hnorm hu)).ne'
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
  exact cumulativeIntegral_densityQuantile hab hf hfnonneg hfpos hnorm
    ⟨hv.1.le, hv.2.le⟩

/-! ## Quantile interpolation and the restricted BBL inequality -/

/-- Pointwise affine interpolation of two real-valued functions. -/
def weightedRealFunction (t : ℝ) (p q : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 - t) * p u + t * q u

theorem continuous_weightedRealFunction {t : ℝ} {p q : ℝ → ℝ}
    (hp : Continuous p) (hq : Continuous q) :
    Continuous (weightedRealFunction t p q) := by
  unfold weightedRealFunction
  exact (continuous_const.mul hp).add (continuous_const.mul hq)

theorem hasDerivAt_weightedRealFunction {t : ℝ} {p q : ℝ → ℝ}
    {p' q' u : ℝ} (hp : HasDerivAt p p' u) (hq : HasDerivAt q q' u) :
    HasDerivAt (weightedRealFunction t p q) ((1 - t) * p' + t * q') u := by
  unfold weightedRealFunction
  exact (hp.const_mul (1 - t)).add (hq.const_mul t)

/-- Restricted one-dimensional Borell--Brascamp--Lieb, in exactly the form
needed by the slicing proof of Brunn--Minkowski.

The functions `r₀` and `r₁` are slice-volume radii: their `q`-th powers
are normalized slice-volume densities.  The hypothesis says that `h` at the
interpolated quantiles dominates the `q`-th power of the interpolated radii.
The conclusion is that `h` has integral at least one on the interpolated
projection interval. -/
theorem one_le_integral_of_quantile_power_lower_bound
    (q : ℕ) {t a₀ b₀ a₁ b₁ : ℝ}
    {r₀ r₁ h : ℝ → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hab₀ : a₀ < b₀) (hab₁ : a₁ < b₁)
    (hr₀ : Continuous r₀) (hr₁ : Continuous r₁) (hh : Continuous h)
    (hr₀nonneg : ∀ x ∈ Icc a₀ b₀, 0 ≤ r₀ x)
    (hr₁nonneg : ∀ x ∈ Icc a₁ b₁, 0 ≤ r₁ x)
    (hr₀pos : ∀ x ∈ Ioo a₀ b₀, 0 < r₀ x)
    (hr₁pos : ∀ x ∈ Ioo a₁ b₁, 0 < r₁ x)
    (hnorm₀ : ∫ x in a₀..b₀, (r₀ x) ^ q = 1)
    (hnorm₁ : ∫ x in a₁..b₁, (r₁ x) ^ q = 1)
    (hlower : ∀ u ∈ Ioo (0 : ℝ) 1,
      ((1 - t) * r₀
          (densityQuantile hab₀ (hr₀.pow q)
            (fun x hx ↦ pow_nonneg (hr₀nonneg x hx) q)
            (fun x hx ↦ pow_pos (hr₀pos x hx) q) hnorm₀ u) +
        t * r₁
          (densityQuantile hab₁ (hr₁.pow q)
            (fun x hx ↦ pow_nonneg (hr₁nonneg x hx) q)
            (fun x hx ↦ pow_pos (hr₁pos x hx) q) hnorm₁ u)) ^ q ≤
        h (weightedRealFunction t
          (densityQuantile hab₀ (hr₀.pow q)
            (fun x hx ↦ pow_nonneg (hr₀nonneg x hx) q)
            (fun x hx ↦ pow_pos (hr₀pos x hx) q) hnorm₀)
          (densityQuantile hab₁ (hr₁.pow q)
            (fun x hx ↦ pow_nonneg (hr₁nonneg x hx) q)
            (fun x hx ↦ pow_pos (hr₁pos x hx) q) hnorm₁) u)) :
    1 ≤ ∫ x in (1 - t) * a₀ + t * a₁..(1 - t) * b₀ + t * b₁, h x := by
  let f₀ : ℝ → ℝ := fun x ↦ (r₀ x) ^ q
  let f₁ : ℝ → ℝ := fun x ↦ (r₁ x) ^ q
  have hf₀ : Continuous f₀ := hr₀.pow q
  have hf₁ : Continuous f₁ := hr₁.pow q
  have hf₀nonneg : ∀ x ∈ Icc a₀ b₀, 0 ≤ f₀ x :=
    fun x hx ↦ pow_nonneg (hr₀nonneg x hx) q
  have hf₁nonneg : ∀ x ∈ Icc a₁ b₁, 0 ≤ f₁ x :=
    fun x hx ↦ pow_nonneg (hr₁nonneg x hx) q
  have hf₀pos : ∀ x ∈ Ioo a₀ b₀, 0 < f₀ x :=
    fun x hx ↦ pow_pos (hr₀pos x hx) q
  have hf₁pos : ∀ x ∈ Ioo a₁ b₁, 0 < f₁ x :=
    fun x hx ↦ pow_pos (hr₁pos x hx) q
  let Q₀ : ℝ → ℝ := densityQuantile hab₀ hf₀ hf₀nonneg hf₀pos hnorm₀
  let Q₁ : ℝ → ℝ := densityQuantile hab₁ hf₁ hf₁nonneg hf₁pos hnorm₁
  let T : ℝ → ℝ := weightedRealFunction t Q₀ Q₁
  let T' : ℝ → ℝ := fun u ↦
    (1 - t) * (f₀ (Q₀ u))⁻¹ + t * (f₁ (Q₁ u))⁻¹
  have hQ₀cont : Continuous Q₀ :=
    continuous_densityQuantile hab₀ hf₀ hf₀nonneg hf₀pos hnorm₀
  have hQ₁cont : Continuous Q₁ :=
    continuous_densityQuantile hab₁ hf₁ hf₁nonneg hf₁pos hnorm₁
  have hTcont : Continuous T :=
    continuous_weightedRealFunction hQ₀cont hQ₁cont
  have hTderiv : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt T (T' u) u := by
    intro u hu
    exact hasDerivAt_weightedRealFunction
      (hasDerivAt_densityQuantile hab₀ hf₀ hf₀nonneg hf₀pos hnorm₀ hu)
      (hasDerivAt_densityQuantile hab₁ hf₁ hf₁nonneg hf₁pos hnorm₁ hu)
  have hT'nonneg : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ T' u := by
    intro u hu
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (inv_nonneg.mpr (hf₀nonneg _
        (densityQuantile_mem_Icc hab₀ hf₀ hf₀nonneg hf₀pos hnorm₀ u))))
      (mul_nonneg ht0 (inv_nonneg.mpr (hf₁nonneg _
        (densityQuantile_mem_Icc hab₁ hf₁ hf₁nonneg hf₁pos hnorm₁ u))))
  have hTderiv_uIoo :
      ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt T (T' u) u := by
    simpa using hTderiv
  have hT'nonneg_uIoo :
      ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ T' u := by
    simpa using hT'nonneg
  have hIntegrable : IntervalIntegrable (fun u ↦ h (T u) * T' u) volume 0 1 := by
    change IntervalIntegrable (fun u ↦ (h ∘ T) u * T' u) volume 0 1
    exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      hTcont.continuousOn hTderiv_uIoo hT'nonneg_uIoo).2
        (hh.intervalIntegrable (T 0) (T 1))
  have hpoint : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ h (T u) * T' u := by
    intro u hu
    have hQ₀int := densityQuantile_mem_Ioo hab₀ hf₀ hf₀nonneg hf₀pos hnorm₀ hu
    have hQ₁int := densityQuantile_mem_Ioo hab₁ hf₁ hf₁nonneg hf₁pos hnorm₁ hu
    have hr₀u : 0 < r₀ (Q₀ u) := hr₀pos _ hQ₀int
    have hr₁u : 0 < r₁ (Q₁ u) := hr₁pos _ hQ₁int
    have hT'u : 0 ≤ T' u := hT'nonneg u hu
    calc
      1 ≤ ((1 - t) * r₀ (Q₀ u) + t * r₁ (Q₁ u)) ^ q * T' u := by
        simpa only [T', f₀, f₁] using
          one_le_weightedPower_mul_weightedInvPower q ht0 ht1 hr₀u hr₁u
      _ ≤ h (T u) * T' u := by
        apply mul_le_mul_of_nonneg_right _ hT'u
        simpa only [Q₀, Q₁, T, f₀, f₁] using hlower u hu
  have hIntegralLower : 1 ≤ ∫ u in (0 : ℝ)..1, h (T u) * T' u := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
      (a := (0 : ℝ)) (b := 1) zero_le_one
      (continuous_const.intervalIntegrable 0 1) hIntegrable hpoint
    simpa using hmono
  have hchange :
      (∫ u in (0 : ℝ)..1, h (T u) * T' u) =
        ∫ x in T 0..T 1, h x := by
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        hTcont.continuousOn hTderiv_uIoo hT'nonneg_uIoo (g := h))
  calc
    1 ≤ ∫ u in (0 : ℝ)..1, h (T u) * T' u := hIntegralLower
    _ = ∫ x in T 0..T 1, h x := hchange
    _ = ∫ x in (1 - t) * a₀ + t * a₁..(1 - t) * b₀ + t * b₁, h x := by
      simp only [T, weightedRealFunction, Q₀, Q₁,
        densityQuantile_zero, densityQuantile_one]

end ZeroOrderBounds.AccuracyImprovement
