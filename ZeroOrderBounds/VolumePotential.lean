import ZeroOrderBounds.OracleState
import ZeroOrderBounds.BallVolumeRatio
import ZeroOrderBounds.GoodRow
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Product-volume potential

This file separates the numerical potential argument from the geometric construction of an
oracle step.  A row body's intrinsic volume is normalized by the volume of the radius-`tau`
ball in its own affine dimension.  The resulting number lies in `(0,1]`.

The iteration theorem below is deliberately abstract: its input is only a trajectory of total
product volumes and a predicate recording informative rounds.  `OracleStep` and the eventual
oracle iterator therefore need only supply the two one-step multiplier inequalities.
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset Metric Set

namespace ZeroOrderBounds

/-! ## Normalized row volume -/

namespace RowBody

/-- Intrinsic volume divided by the radius-`tau` ball volume in the row body's affine
dimension. -/
def normalizedVolume {m : ℕ} (P : RowBody m) : ℝ :=
  P.volumeReal / (kappaReal P.dim * tau m ^ P.dim)

theorem normalizer_pos {m : ℕ} (hm : 0 < m) (P : RowBody m) :
    0 < kappaReal P.dim * tau m ^ P.dim := by
  exact mul_pos (kappaReal_pos P.dim) (pow_pos (tau_pos hm) P.dim)

theorem normalizedVolume_pos {m : ℕ} (hm : 0 < m) (P : RowBody m) :
    0 < P.normalizedVolume := by
  exact div_pos P.volumeReal_pos (P.normalizer_pos hm)

/-- A row body occupies at most the full relative ball of radius `tau`. -/
theorem volumeReal_le_normalizer {m : ℕ} (hm : 0 < m) (P : RowBody m) :
    P.volumeReal ≤ kappaReal P.dim * tau m ^ P.dim := by
  have hvol :
      P.body.volume ≤ ENNReal.ofReal (tau m) ^ P.body.dim * kappa P.body.dim :=
    P.body.volume_le_of_subset_closedBall P.subset_initial
  have htop : ENNReal.ofReal (tau m) ^ P.body.dim * kappa P.body.dim ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (kappa_lt_top P.body.dim).ne
  have hreal := ENNReal.toReal_mono htop hvol
  simpa [RowBody.volumeReal, RowBody.dim, IntrinsicBody.volumeReal,
    IntrinsicBody.volume, intrinsicVolumeReal, kappaReal, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (tau_pos hm).le, mul_comm] using hreal

theorem normalizedVolume_le_one {m : ℕ} (hm : 0 < m) (P : RowBody m) :
    P.normalizedVolume ≤ 1 := by
  rw [normalizedVolume, div_le_one (P.normalizer_pos hm)]
  exact P.volumeReal_le_normalizer hm

theorem normalizedVolume_mem_Ioc {m : ℕ} (hm : 0 < m) (P : RowBody m) :
    P.normalizedVolume ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨P.normalizedVolume_pos hm, P.normalizedVolume_le_one hm⟩

end RowBody

/-- The initial full-dimensional row ball has exactly the expected Euclidean volume. -/
theorem initialRowBody_volumeReal_eq {m : ℕ} (hm : 0 < m) :
    (initialRowBody m).volumeReal = kappaReal m * tau m ^ m := by
  have hdim := initialRowBody.dim_eq hm
  have haff :
      affineDim (closedBall (0 : RowSpace m) (tau m)) = m := by
    change affineDim ((initialRowBody m : RowBody m) : Set (RowSpace m)) = m at hdim
    rw [initialRowBody.carrier] at hdim
    exact hdim
  have haff0 : affineDim (closedBall (0 : RowSpace m) (tau m)) ≠ 0 := by
    rw [haff]
    exact hm.ne'
  change intrinsicVolumeReal (closedBall (0 : RowSpace m) (tau m)) = _
  rw [intrinsicVolumeReal, intrinsicVolume_of_affineDim_ne_zero haff0, haff,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    volume_closedBall_eq_ofReal_pow_mul_kappa m (tau_pos hm).le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (tau_pos hm).le m)]
  rw [kappaReal]
  ring

@[simp]
theorem initialRowBody_normalizedVolume {m : ℕ} (hm : 0 < m) :
    (initialRowBody m).normalizedVolume = 1 := by
  rw [RowBody.normalizedVolume, initialRowBody_volumeReal_eq hm,
    initialRowBody.dim_eq hm]
  exact div_self (mul_ne_zero (kappaReal_pos m).ne' (pow_pos (tau_pos hm) m).ne')

/-! ## Abstract multiplicative iteration -/

/-- Number of informative rounds among the first `T` natural-number-indexed rounds. -/
def informativeCount (T : ℕ) (informative : ℕ → Prop) [DecidablePred informative] : ℕ :=
  ((Finset.range T).filter informative).card

@[simp]
theorem informativeCount_zero (informative : ℕ → Prop) [DecidablePred informative] :
    informativeCount 0 informative = 0 := by
  simp [informativeCount]

theorem informativeCount_succ (T : ℕ) (informative : ℕ → Prop)
    [DecidablePred informative] :
    informativeCount (T + 1) informative =
      informativeCount T informative + if informative T then 1 else 0 := by
  unfold informativeCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hT : informative T
  · simp [hT]
  · simp [hT]

theorem informativeCount_le (T : ℕ) (informative : ℕ → Prop)
    [DecidablePred informative] : informativeCount T informative ≤ T := by
  simpa [informativeCount] using
    Finset.card_filter_le (Finset.range T) informative

/-- Generic multiplicative induction.  An informative step pays both `base` and `extra`; any
other step pays only `base`. -/
theorem iterate_product_lower_bound
    {V : ℕ → ℝ} {informative : ℕ → Prop} [DecidablePred informative]
    {initial base extra : ℝ} (hbase : 0 ≤ base) (hextra : 0 ≤ extra)
    (hinitial : initial ≤ V 0)
    (hstep : ∀ t : ℕ,
      if informative t then base * extra * V t ≤ V (t + 1)
      else base * V t ≤ V (t + 1)) (T : ℕ) :
    initial * base ^ T * extra ^ informativeCount T informative ≤ V T := by
  induction T with
  | zero => simpa using hinitial
  | succ T ih =>
      by_cases hT : informative T
      · have hmul :
            base * extra * (initial * base ^ T *
              extra ^ informativeCount T informative) ≤
              base * extra * V T :=
          mul_le_mul_of_nonneg_left ih (mul_nonneg hbase hextra)
        calc
          initial * base ^ (T + 1) *
                extra ^ informativeCount (T + 1) informative =
              base * extra * (initial * base ^ T *
                extra ^ informativeCount T informative) := by
            rw [informativeCount_succ, if_pos hT, pow_succ, pow_succ]
            ring
          _ ≤ base * extra * V T := hmul
          _ ≤ V (T + 1) := by simpa [hT] using hstep T
      · have hmul :
            base * (initial * base ^ T *
              extra ^ informativeCount T informative) ≤ base * V T :=
          mul_le_mul_of_nonneg_left ih hbase
        calc
          initial * base ^ (T + 1) *
                extra ^ informativeCount (T + 1) informative =
              base * (initial * base ^ T *
                extra ^ informativeCount T informative) := by
            rw [informativeCount_succ, if_neg hT, pow_succ]
            ring
          _ ≤ base * V T := hmul
          _ ≤ V (T + 1) := by simpa [hT] using hstep T

/-! ## The oracle's raw one-step multipliers -/

/-- Fraction retained by every unselected, nonconstant row. -/
def retention (m : ℕ) : ℝ :=
  1 - 1 / (4 * (m : ℝ))

theorem retention_nonneg {m : ℕ} (hm : 0 < m) : 0 ≤ retention m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold retention
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hfrac : 1 / (4 * (m : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith
  linarith

theorem retention_le_one (m : ℕ) : retention m ≤ 1 := by
  unfold retention
  exact sub_le_self 1 (by positivity)

/-- Bernoulli's inequality gives the uniform `3/4` product-retention factor. -/
theorem three_fourths_le_retention_pow {m : ℕ} (hm : 0 < m) :
    (3 / 4 : ℝ) ≤ retention m ^ m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmRone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : 1 / (4 * (m : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * (m : ℝ))]
    nlinarith
  have hbern := one_sub_mul_le_pow m hx
  have hid : 1 - (m : ℝ) * (1 / (4 * (m : ℝ))) = (3 / 4 : ℝ) := by
    field_simp [hmR.ne']; ring
  calc
    (3 / 4 : ℝ) = 1 - (m : ℝ) * (1 / (4 * (m : ℝ))) := hid.symm
    _ ≤ (1 - 1 / (4 * (m : ℝ))) ^ m := hbern
    _ = retention m ^ m := rfl

theorem three_fourths_le_retention_pow_pred {m : ℕ} (hm : 0 < m) :
    (3 / 4 : ℝ) ≤ retention m ^ (m - 1) := by
  exact (three_fourths_le_retention_pow hm).trans
    (pow_le_pow_of_le_one (retention_nonneg hm) (retention_le_one m)
      (Nat.sub_le m 1))

/-- Raw informative/noninformative oracle multipliers imply the clean product-volume bound
(17.1).  `V t` is the total product of row volumes after `t` rounds. -/
theorem productVolume_lower_of_oracle_steps
    {m T : ℕ} (hm : 0 < m) {V : ℕ → ℝ}
    {informative : ℕ → Prop} [DecidablePred informative]
    (hVnonneg : ∀ t, 0 ≤ V t)
    (hinitial : (kappaReal m * tau m ^ m) ^ m ≤ V 0)
    (hstep : ∀ t : ℕ,
      if informative t then
        (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) * V t ≤ V (t + 1)
      else retention m ^ m * V t ≤ V (t + 1)) :
    (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
        (1 / (8 * (m : ℝ) * tau m)) ^ informativeCount T informative ≤ V T := by
  have hextra : 0 ≤ 1 / (8 * (m : ℝ) * tau m) := by positivity [tau_pos hm]
  apply iterate_product_lower_bound (initial := (kappaReal m * tau m ^ m) ^ m)
    (base := (3 / 4 : ℝ)) (extra := 1 / (8 * (m : ℝ) * tau m))
    (by norm_num) hextra hinitial (T := T)
  intro t
  by_cases ht : informative t
  · simp only [ht, if_true]
    calc
      (3 / 4 : ℝ) * (1 / (8 * (m : ℝ) * tau m)) * V t =
          (1 / (8 * (m : ℝ) * tau m)) * (3 / 4 : ℝ) * V t := by ring
      _ ≤ (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) * V t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (three_fourths_le_retention_pow_pred hm) hextra)
          (hVnonneg t)
      _ ≤ V (t + 1) := by simpa [ht] using hstep t
  · simp only [ht, if_false]
    calc
      (3 / 4 : ℝ) * V t ≤ retention m ^ m * V t :=
        mul_le_mul_of_nonneg_right (three_fourths_le_retention_pow hm) (hVnonneg t)
      _ ≤ V (t + 1) := by simpa [ht] using hstep t

/-! ## Cancellation of dimensions and normalization -/

/-- Product of all radius-`tau` intrinsic ball normalizers.  The ball-volume ratio estimate
charges at most `2 * sqrt m / tau` for each unit of total codimension. -/
theorem product_row_normalizers_le
    {m s : ℕ} (hm : 0 < m) (k c : Fin m → ℕ)
    (hc : ∀ i, c i ≤ m) (hk : ∀ i, k i = m - c i)
    (hcsum : ∑ i, c i = s) :
    (∏ i, kappaReal (k i) * tau m ^ k i) ≤
      (kappaReal m * tau m ^ m) ^ m *
        ((2 * Real.sqrt (m : ℝ)) / tau m) ^ s := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htau : 0 < tau m := tau_pos hm
  have hR : 0 < 2 * Real.sqrt (m : ℝ) := by positivity
  calc
    (∏ i, kappaReal (k i) * tau m ^ k i) ≤
        ∏ i, (kappaReal m * tau m ^ m) *
          ((2 * Real.sqrt (m : ℝ)) / tau m) ^ c i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mul_nonneg (kappaReal_nonneg (k i)) (pow_nonneg htau.le (k i))
      · intro i hi
        have hki : k i ≤ m := by rw [hk i]; exact Nat.sub_le m (c i)
        have hkappa := kappaReal_div_pow_sqrt_le hki
        have hpow : 0 < (2 * Real.sqrt (m : ℝ)) ^ (m - k i) := pow_pos hR _
        rw [div_le_iff₀ hpow] at hkappa
        have hcodim : m - k i = c i := by
          rw [hk i, Nat.sub_sub_self (hc i)]
        rw [hcodim] at hkappa
        calc
          kappaReal (k i) * tau m ^ k i ≤
              (kappaReal m * (2 * Real.sqrt (m : ℝ)) ^ c i) * tau m ^ k i :=
            mul_le_mul_of_nonneg_right hkappa (pow_nonneg htau.le (k i))
          _ = (kappaReal m * tau m ^ m) *
              ((2 * Real.sqrt (m : ℝ)) / tau m) ^ c i := by
            rw [hk i, pow_sub₀ (tau m) htau.ne' (hc i), div_pow]
            field_simp
    _ = (kappaReal m * tau m ^ m) ^ m *
        ((2 * Real.sqrt (m : ℝ)) / tau m) ^ s := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_pow_eq_pow_sum, hcsum]
      simp

/-- Pure normalized-volume conversion.  Starting from (17.1), the powers of `tau` cancel and
the telescoped unit-ball comparison yields (17.3). -/
theorem normalized_product_lower
    {m T s : ℕ} (hm : 0 < m) (V : Fin m → ℝ) (k c : Fin m → ℕ)
    (hc : ∀ i, c i ≤ m) (hk : ∀ i, k i = m - c i)
    (hcsum : ∑ i, c i = s)
    (hvolume :
      (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
          (1 / (8 * (m : ℝ) * tau m)) ^ s ≤ ∏ i, V i) :
    (3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s ≤
      ∏ i, V i / (kappaReal (k i) * tau m ^ k i) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htau : 0 < tau m := tau_pos hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  let D : ℝ := ∏ i, kappaReal (k i) * tau m ^ k i
  have hDpos : 0 < D := by
    apply Finset.prod_pos
    intro i hi
    exact mul_pos (kappaReal_pos (k i)) (pow_pos htau (k i))
  have hD := product_row_normalizers_le hm k c hc hk hcsum
  have hloss :
      (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) *
          ((2 * Real.sqrt (m : ℝ)) / tau m) =
        1 / (8 * (m : ℝ) * tau m) := by
    field_simp [hmR.ne', hsqrt.ne', htau.ne']; ring
  rw [Finset.prod_div_distrib, le_div_iff₀ hDpos]
  change
    (3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s * D ≤ ∏ i, V i
  apply le_trans ?_ hvolume
  calc
    (3 / 4 : ℝ) ^ T *
          (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s * D ≤
        (3 / 4 : ℝ) ^ T *
          (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s *
            ((kappaReal m * tau m ^ m) ^ m *
              ((2 * Real.sqrt (m : ℝ)) / tau m) ^ s) := by
      exact mul_le_mul_of_nonneg_left hD
        (mul_nonneg (pow_nonneg (by norm_num) T) (pow_nonneg (by positivity) s))
    _ = (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
          (1 / (8 * (m : ℝ) * tau m)) ^ s := by
      calc
        _ = (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
            ((1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s *
              ((2 * Real.sqrt (m : ℝ)) / tau m) ^ s) := by ring
        _ = (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
            ((1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ)) *
              ((2 * Real.sqrt (m : ℝ)) / tau m)) ^ s) := by
          congr 1
          exact (mul_pow _ _ s).symm
        _ = _ := by rw [hloss]

/-- Specialization of `normalized_product_lower` to actual final row bodies. -/
theorem normalized_product_lower_of_rowBodies
    {m T s : ℕ} (hm : 0 < m) (rows : Fin m → RowBody m) (c : Fin m → ℕ)
    (hc : ∀ i, c i ≤ m) (hdim : ∀ i, (rows i).dim = m - c i)
    (hcsum : ∑ i, c i = s)
    (hvolume :
      (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
          (1 / (8 * (m : ℝ) * tau m)) ^ s ≤
        ∏ i, (rows i).volumeReal) :
    (3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s ≤
      ∏ i, (rows i).normalizedVolume := by
  simpa [RowBody.normalizedVolume] using
    normalized_product_lower hm (fun i ↦ (rows i).volumeReal)
      (fun i ↦ (rows i).dim) c hc hdim hcsum hvolume

/-! ## Entropy form of the potential -/

/-- Taking logarithms of (17.3), with the number of informative rounds bounded by the horizon,
gives the entropy budget (17.5).  Positivity of both factors on the left of (17.3) is recorded
explicitly before `Real.log` is used. -/
theorem entropy_sum_le_of_normalized_product
    {m T s : ℕ} (hm : 0 < m) (hsT : s ≤ T) (rho : Fin m → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hproduct :
      (3 / 4 : ℝ) ^ T *
          (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s ≤ ∏ i, rho i) :
    ∑ i, rowEntropy (rho i) ≤ (T : ℝ) * entropyScale m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmRone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsqrt_one : 1 ≤ Real.sqrt (m : ℝ) := by
    rw [Real.le_sqrt (by norm_num)]
    · simpa using hmRone
    · norm_num
  have hargpos : 0 < 16 * (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
  have hargone : 1 ≤ 16 * (m : ℝ) * Real.sqrt (m : ℝ) := by
    have h16m : (16 : ℝ) ≤ 16 * (m : ℝ) := by nlinarith
    have hcoef : 0 ≤ 16 * (m : ℝ) := mul_nonneg (by norm_num) hmR.le
    have hmul := mul_le_mul_of_nonneg_left hsqrt_one hcoef
    linarith
  have hbasepos : (0 : ℝ) < 3 / 4 := by norm_num
  have hlosspos :
      0 < 1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by positivity
  have hlowerpos :
      0 < (3 / 4 : ℝ) ^ T *
          (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s :=
    mul_pos (pow_pos hbasepos T) (pow_pos hlosspos s)
  have hlogmono := Real.log_le_log hlowerpos hproduct
  have hlogbase : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlogloss :
      Real.log (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) =
        -Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [one_div, Real.log_inv]
  have hloglower :
      Real.log ((3 / 4 : ℝ) ^ T *
          (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s) =
        -(T : ℝ) * Real.log (4 / 3 : ℝ) -
          (s : ℝ) * Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [Real.log_mul (pow_ne_zero T hbasepos.ne') (pow_ne_zero s hlosspos.ne'),
      Real.log_pow, Real.log_pow, hlogbase, hlogloss]
    ring
  have hsum :
      ∑ i, rowEntropy (rho i) = -Real.log (∏ i, rho i) := by
    calc
      ∑ i, rowEntropy (rho i) = -∑ i, Real.log (rho i) := by
        simp [rowEntropy]
      _ = -Real.log (∏ i, rho i) := by
        rw [Real.log_prod (fun i _ ↦ (hrho i).ne')]
  have hsR : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
  have hlogarg : 0 ≤ Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) :=
    Real.log_nonneg hargone
  calc
    ∑ i, rowEntropy (rho i) = -Real.log (∏ i, rho i) := hsum
    _ ≤ -Real.log ((3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^ s) :=
      neg_le_neg hlogmono
    _ = (T : ℝ) * Real.log (4 / 3 : ℝ) +
        (s : ℝ) * Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by
      rw [hloglower]
      ring
    _ ≤ (T : ℝ) * Real.log (4 / 3 : ℝ) +
        (T : ℝ) * Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsR hlogarg)
    _ = (T : ℝ) * entropyScale m := by
      rw [entropyScale_eq_log_add hm]
      ring

/-! ## Complete abstract oracle potential -/

/-- End-to-end potential theorem for a future oracle iterator.

The trajectory `totalVolume t` is the product of all row volumes after `t` rounds.  Its initial
value is supplied as the product of the full radius-`tau` balls, its final value as the product of
the bundled final row bodies, and each round satisfies exactly the informative/noninformative
multiplier proved by `OracleStep`.  Selection counts supply the dimension identities and sum to
the number of informative rounds. -/
theorem volumePotential_of_oracle_steps
    {m T : ℕ} (hm : 0 < m) {totalVolume : ℕ → ℝ}
    {informative : ℕ → Prop} [DecidablePred informative]
    (rows : Fin m → RowBody m) (c : Fin m → ℕ)
    (hTotalNonneg : ∀ t, 0 ≤ totalVolume t)
    (hinitial :
      totalVolume 0 = ∏ _i : Fin m, (initialRowBody m).volumeReal)
    (hstep : ∀ t : ℕ,
      if informative t then
        (1 / (8 * (m : ℝ) * tau m)) * retention m ^ (m - 1) *
            totalVolume t ≤ totalVolume (t + 1)
      else retention m ^ m * totalVolume t ≤ totalVolume (t + 1))
    (hfinal : totalVolume T = ∏ i, (rows i).volumeReal)
    (hc : ∀ i, c i ≤ m)
    (hdim : ∀ i, (rows i).dim = m - c i)
    (hcsum : ∑ i, c i = informativeCount T informative) :
    ((3 / 4 : ℝ) ^ T *
        (1 / (16 * (m : ℝ) * Real.sqrt (m : ℝ))) ^
          informativeCount T informative ≤
        ∏ i, (rows i).normalizedVolume) ∧
      (∑ i, rowEntropy ((rows i).normalizedVolume) ≤
        (T : ℝ) * entropyScale m) := by
  have hinitial' :
      (kappaReal m * tau m ^ m) ^ m ≤ totalVolume 0 := by
    rw [hinitial]
    simp [initialRowBody_volumeReal_eq hm]
  have htotal := productVolume_lower_of_oracle_steps
    (T := T) hm hTotalNonneg hinitial' hstep
  have hvolume :
      (kappaReal m * tau m ^ m) ^ m * (3 / 4 : ℝ) ^ T *
          (1 / (8 * (m : ℝ) * tau m)) ^ informativeCount T informative ≤
        ∏ i, (rows i).volumeReal := by
    exact htotal.trans_eq hfinal
  have hnormalized := normalized_product_lower_of_rowBodies
    hm rows c hc hdim hcsum hvolume
  refine ⟨hnormalized, ?_⟩
  exact entropy_sum_le_of_normalized_product hm
    (informativeCount_le T informative) (fun i ↦ (rows i).normalizedVolume)
    (fun i ↦ (rows i).normalizedVolume_pos hm) hnormalized

end ZeroOrderBounds
