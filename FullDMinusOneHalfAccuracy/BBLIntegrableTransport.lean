import FullDMinusOneHalfAccuracy.ConcaveDensityTransport
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# BBL transport with possibly discontinuous endpoint densities

Hyperplane-section volumes of a convex body are continuous in the interior
of the projection interval, but endpoint continuity is an unnecessary and
awkward extra obligation.  This file strengthens the transport layer to
interval-integrable densities which are continuous and positive only on the
open support interval.  Endpoint values are measure-zero data.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace ZeroOrderBounds.AccuracyImprovement

/-- An interval-integrable density has a continuous cumulative integral on
its whole support interval, regardless of its endpoint values. -/
theorem continuousOn_cumulativeIntegral_Icc_of_intervalIntegrable
    {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b) :
    ContinuousOn (cumulativeIntegral a f) (Icc a b) := by
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hAC := hfi.absolutelyContinuousOnInterval_intervalIntegral ha
  change ContinuousOn (fun x ↦ ∫ v in a..x, f v) (Icc a b)
  simpa only [uIcc_of_le hab] using hAC.continuousOn

/-- Difference formula for cumulative integrals under local interval
integrability. -/
theorem cumulativeIntegral_sub_of_intervalIntegrable
    {a b x y : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfi : IntervalIntegrable f volume a b) :
    cumulativeIntegral a f y - cumulativeIntegral a f x =
      ∫ u in x..y, f u := by
  simp only [cumulativeIntegral]
  apply intervalIntegral.integral_interval_sub_left
  · apply hfi.mono_set
    rw [uIcc_of_le hab, uIcc_of_le hy.1]
    exact Icc_subset_Icc_right hy.2
  · apply hfi.mono_set
    rw [uIcc_of_le hab, uIcc_of_le hx.1]
    exact Icc_subset_Icc_right hx.2

/-- Positivity in the open support makes the cumulative integral strictly
increasing; no endpoint regularity is needed. -/
theorem strictMonoOn_cumulativeIntegral_of_intervalIntegrable
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (cumulativeIntegral a f) (Icc a b) := by
  intro x hx y hy hxy
  rw [← sub_pos,
    cumulativeIntegral_sub_of_intervalIntegrable hab.le hx hy hfi]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply hfi.mono_set
    rw [uIcc_of_le hab.le, uIcc_of_le hxy.le]
    exact Icc_subset_Icc hx.1 hy.2
  · intro z hz
    exact hfpos z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  · exact hxy

/-- The image of a normalized integrable cumulative density is `[0,1]`. -/
theorem cumulativeIntegral_image_Icc_of_intervalIntegrable
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    cumulativeIntegral a f '' Icc a b = Icc 0 1 := by
  have hcont := continuousOn_cumulativeIntegral_Icc_of_intervalIntegrable hab.le hfi
  rw [hcont.image_Icc_of_monotoneOn hab.le
    (strictMonoOn_cumulativeIntegral_of_intervalIntegrable hab hfi hfpos).monotoneOn]
  simp [cumulativeIntegral, hnorm]

/-- Order isomorphism furnished by a normalized density which is positive
and continuous only in the open interval.  Continuity is used below for the
inverse derivative, not for construction of the order isomorphism. -/
noncomputable def integrableDensityOrderIso
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    Icc a b ≃o Icc (0 : ℝ) 1 :=
  (strictMonoOn_cumulativeIntegral_of_intervalIntegrable hab hfi hfpos).orderIso
      (cumulativeIntegral a f) (Icc a b) |>.trans
    (OrderIso.setCongr _ _
      (cumulativeIntegral_image_Icc_of_intervalIntegrable hab hfi hfpos hnorm))

@[simp]
theorem integrableDensityOrderIso_apply_coe
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) (x : Icc a b) :
    ((integrableDensityOrderIso hab hfi hfpos hnorm x : Icc (0 : ℝ) 1) : ℝ) =
      cumulativeIntegral a f x :=
  rfl

/-- Clamped inverse CDF for an interval-integrable density. -/
noncomputable def integrableDensityQuantile
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) : ℝ → ℝ :=
  Subtype.val ∘ IccExtend (zero_le_one' ℝ)
    (integrableDensityOrderIso hab hfi hfpos hnorm).symm

theorem continuous_integrableDensityQuantile
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    Continuous (integrableDensityQuantile hab hfi hfpos hnorm) :=
  continuous_subtype_val.comp
    (integrableDensityOrderIso hab hfi hfpos hnorm).symm.continuous.Icc_extend'

theorem integrableDensityQuantile_mem_Icc
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) (u : ℝ) :
    integrableDensityQuantile hab hfi hfpos hnorm u ∈ Icc a b :=
  Subtype.coe_prop _

theorem cumulativeIntegral_integrableDensityQuantile
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    cumulativeIntegral a f (integrableDensityQuantile hab hfi hfpos hnorm u) = u := by
  let e := integrableDensityOrderIso hab hfi hfpos hnorm
  have he := e.apply_symm_apply ⟨u, hu⟩
  apply Subtype.ext_iff.mp at he
  simpa only [e, integrableDensityQuantile, Function.comp_apply,
    IccExtend_of_mem (zero_le_one' ℝ) _ hu,
    integrableDensityOrderIso_apply_coe] using he

theorem integrableDensityQuantile_cumulativeIntegral
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1)
    {x : ℝ} (hx : x ∈ Icc a b) :
    integrableDensityQuantile hab hfi hfpos hnorm (cumulativeIntegral a f x) = x := by
  let e := integrableDensityOrderIso hab hfi hfpos hnorm
  have hc : cumulativeIntegral a f x ∈ Icc (0 : ℝ) 1 := by
    simpa only [e, integrableDensityOrderIso_apply_coe] using (e ⟨x, hx⟩).property
  rw [integrableDensityQuantile, Function.comp_apply,
    IccExtend_of_mem (zero_le_one' ℝ) _ hc]
  change ↑(e.symm ⟨cumulativeIntegral a f x, hc⟩) = x
  have harg : (⟨cumulativeIntegral a f x, hc⟩ : Icc (0 : ℝ) 1) = e ⟨x, hx⟩ := by
    ext
    rfl
  rw [harg, e.symm_apply_apply]

@[simp]
theorem integrableDensityQuantile_zero
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    integrableDensityQuantile hab hfi hfpos hnorm 0 = a := by
  simpa only [cumulativeIntegral_left] using
    (integrableDensityQuantile_cumulativeIntegral hab hfi hfpos hnorm
      (x := a) ⟨le_rfl, hab.le⟩)

@[simp]
theorem integrableDensityQuantile_one
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1) :
    integrableDensityQuantile hab hfi hfpos hnorm 1 = b := by
  simpa only [cumulativeIntegral_right hnorm] using
    (integrableDensityQuantile_cumulativeIntegral hab hfi hfpos hnorm
      (x := b) ⟨hab.le, le_rfl⟩)

theorem integrableDensityQuantile_mem_Ioo
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    integrableDensityQuantile hab hfi hfpos hnorm u ∈ Ioo a b := by
  have hq := integrableDensityQuantile_mem_Icc hab hfi hfpos hnorm u
  have hinv := cumulativeIntegral_integrableDensityQuantile hab hfi hfpos hnorm
    ⟨hu.1.le, hu.2.le⟩
  constructor
  · exact lt_of_le_of_ne hq.1 fun hqa ↦ by
      rw [← hqa, cumulativeIntegral_left] at hinv
      exact hu.1.ne' hinv.symm
  · exact lt_of_le_of_ne hq.2 fun hqb ↦ by
      rw [hqb, cumulativeIntegral_right hnorm] at hinv
      exact hu.2.ne hinv.symm

/-- Inverse-CDF derivative under only interior continuity of the density. -/
theorem hasDerivAt_integrableDensityQuantile
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hfcont : ContinuousOn f (Ioo a b))
    (hfpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hnorm : ∫ u in a..b, f u = 1)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (integrableDensityQuantile hab hfi hfpos hnorm)
      (f (integrableDensityQuantile hab hfi hfpos hnorm u))⁻¹ u := by
  let Q := integrableDensityQuantile hab hfi hfpos hnorm
  have hQint : Q u ∈ Ioo a b :=
    integrableDensityQuantile_mem_Ioo hab hfi hfpos hnorm hu
  have hfQcont : ContinuousAt f (Q u) :=
    hfcont.continuousAt (Ioo_mem_nhds hQint.1 hQint.2)
  have hfiQ : IntervalIntegrable f volume a (Q u) := by
    apply hfi.mono_set
    rw [uIcc_of_le hab.le, uIcc_of_le
      (integrableDensityQuantile_mem_Icc hab hfi hfpos hnorm u).1]
    exact Icc_subset_Icc_right
      (integrableDensityQuantile_mem_Icc hab hfi hfpos hnorm u).2
  have hCDFderiv : HasDerivAt (cumulativeIntegral a f) (f (Q u)) (Q u) := by
    exact intervalIntegral.integral_hasDerivAt_right hfiQ
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfcont (Q u) hQint)
      hfQcont
  apply HasDerivAt.of_local_left_inverse
    (continuous_integrableDensityQuantile hab hfi hfpos hnorm).continuousAt
    hCDFderiv (hfpos _ hQint).ne'
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
  exact cumulativeIntegral_integrableDensityQuantile hab hfi hfpos hnorm
    ⟨hv.1.le, hv.2.le⟩

/-! ## Endpoint-robust BBL -/

/-- The restricted BBL theorem for slice radii which need only be continuous
and positive in the interiors of their support intervals.  In particular,
no continuity or even nonnegativity hypothesis is imposed at the two
measure-zero endpoints. -/
theorem one_le_integral_of_integrable_quantile_power_lower_bound
    (q : ℕ) {t a₀ b₀ a₁ b₁ : ℝ}
    {r₀ r₁ h : ℝ → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hab₀ : a₀ < b₀) (hab₁ : a₁ < b₁)
    (hr₀i : IntervalIntegrable (fun x ↦ (r₀ x) ^ q) volume a₀ b₀)
    (hr₁i : IntervalIntegrable (fun x ↦ (r₁ x) ^ q) volume a₁ b₁)
    (hr₀cont : ContinuousOn r₀ (Ioo a₀ b₀))
    (hr₁cont : ContinuousOn r₁ (Ioo a₁ b₁))
    (hhi : IntervalIntegrable h volume
      ((1 - t) * a₀ + t * a₁) ((1 - t) * b₀ + t * b₁))
    (hr₀pos : ∀ x ∈ Ioo a₀ b₀, 0 < r₀ x)
    (hr₁pos : ∀ x ∈ Ioo a₁ b₁, 0 < r₁ x)
    (hnorm₀ : ∫ x in a₀..b₀, (r₀ x) ^ q = 1)
    (hnorm₁ : ∫ x in a₁..b₁, (r₁ x) ^ q = 1)
    (hlower : ∀ u ∈ Ioo (0 : ℝ) 1,
      ((1 - t) * r₀
          (integrableDensityQuantile hab₀ hr₀i
            (fun x hx ↦ pow_pos (hr₀pos x hx) q) hnorm₀ u) +
        t * r₁
          (integrableDensityQuantile hab₁ hr₁i
            (fun x hx ↦ pow_pos (hr₁pos x hx) q) hnorm₁ u)) ^ q ≤
        h (weightedRealFunction t
          (integrableDensityQuantile hab₀ hr₀i
            (fun x hx ↦ pow_pos (hr₀pos x hx) q) hnorm₀)
          (integrableDensityQuantile hab₁ hr₁i
            (fun x hx ↦ pow_pos (hr₁pos x hx) q) hnorm₁) u)) :
    1 ≤ ∫ x in (1 - t) * a₀ + t * a₁..(1 - t) * b₀ + t * b₁, h x := by
  let f₀ : ℝ → ℝ := fun x ↦ (r₀ x) ^ q
  let f₁ : ℝ → ℝ := fun x ↦ (r₁ x) ^ q
  have hf₀cont : ContinuousOn f₀ (Ioo a₀ b₀) := hr₀cont.pow q
  have hf₁cont : ContinuousOn f₁ (Ioo a₁ b₁) := hr₁cont.pow q
  have hf₀pos : ∀ x ∈ Ioo a₀ b₀, 0 < f₀ x :=
    fun x hx ↦ pow_pos (hr₀pos x hx) q
  have hf₁pos : ∀ x ∈ Ioo a₁ b₁, 0 < f₁ x :=
    fun x hx ↦ pow_pos (hr₁pos x hx) q
  let Q₀ : ℝ → ℝ := integrableDensityQuantile hab₀ hr₀i hf₀pos hnorm₀
  let Q₁ : ℝ → ℝ := integrableDensityQuantile hab₁ hr₁i hf₁pos hnorm₁
  let T : ℝ → ℝ := weightedRealFunction t Q₀ Q₁
  let T' : ℝ → ℝ := fun u ↦
    (1 - t) * (f₀ (Q₀ u))⁻¹ + t * (f₁ (Q₁ u))⁻¹
  have hQ₀cont : Continuous Q₀ :=
    continuous_integrableDensityQuantile hab₀ hr₀i hf₀pos hnorm₀
  have hQ₁cont : Continuous Q₁ :=
    continuous_integrableDensityQuantile hab₁ hr₁i hf₁pos hnorm₁
  have hTcont : Continuous T :=
    continuous_weightedRealFunction hQ₀cont hQ₁cont
  have hTderiv : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt T (T' u) u := by
    intro u hu
    exact hasDerivAt_weightedRealFunction
      (hasDerivAt_integrableDensityQuantile hab₀ hr₀i hf₀cont hf₀pos hnorm₀ hu)
      (hasDerivAt_integrableDensityQuantile hab₁ hr₁i hf₁cont hf₁pos hnorm₁ hu)
  have hT'nonneg : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ T' u := by
    intro u hu
    have hQ₀int := integrableDensityQuantile_mem_Ioo hab₀ hr₀i hf₀pos hnorm₀ hu
    have hQ₁int := integrableDensityQuantile_mem_Ioo hab₁ hr₁i hf₁pos hnorm₁ hu
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (inv_nonneg.mpr (hf₀pos _ hQ₀int).le))
      (mul_nonneg ht0 (inv_nonneg.mpr (hf₁pos _ hQ₁int).le))
  have hTderiv_uIoo :
      ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt T (T' u) u := by
    simpa using hTderiv
  have hT'nonneg_uIoo :
      ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ T' u := by
    simpa using hT'nonneg
  have hhiT : IntervalIntegrable h volume (T 0) (T 1) := by
    simpa only [T, weightedRealFunction, Q₀, Q₁,
      integrableDensityQuantile_zero, integrableDensityQuantile_one] using hhi
  have hIntegrable : IntervalIntegrable (fun u ↦ h (T u) * T' u) volume 0 1 := by
    change IntervalIntegrable (fun u ↦ (h ∘ T) u * T' u) volume 0 1
    exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      hTcont.continuousOn hTderiv_uIoo hT'nonneg_uIoo).2
        hhiT
  have hpoint : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ h (T u) * T' u := by
    intro u hu
    have hQ₀int := integrableDensityQuantile_mem_Ioo hab₀ hr₀i hf₀pos hnorm₀ hu
    have hQ₁int := integrableDensityQuantile_mem_Ioo hab₁ hr₁i hf₁pos hnorm₁ hu
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
        integrableDensityQuantile_zero, integrableDensityQuantile_one]

end ZeroOrderBounds.AccuracyImprovement
