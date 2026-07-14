import ZeroOrderBounds.IntrinsicVolume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Ratios of Euclidean unit-ball volumes

The ENNReal-valued constant `kappa` is defined in `IntrinsicVolume`.  Here we establish its
positivity and finiteness and prove the deliberately weak consecutive-dimension estimate needed by
the oracle potential.  The proof places a product cylinder inside the next-dimensional unit ball.
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Metric Set

namespace ZeroOrderBounds

/-- `kappa` is the volume of the closed Euclidean unit ball also in dimension zero. -/
theorem kappa_eq_volume_closedBall (k : ℕ) :
    kappa k = volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  by_cases hk : k = 0
  · subst k
    rw [kappa_zero, volume_euclideanSpace_eq_dirac]
    simp
  · exact kappa_of_ne_zero hk

theorem kappa_ne_zero (k : ℕ) : kappa k ≠ 0 :=
  (kappa_pos k).ne'

theorem kappa_ne_top (k : ℕ) : kappa k ≠ ⊤ :=
  (kappa_lt_top k).ne

theorem kappaReal_nonneg (k : ℕ) : 0 ≤ kappaReal k :=
  (kappaReal_pos k).le

/-- Scaling law for Euclidean closed balls, including dimension zero. -/
theorem volume_closedBall_eq_ofReal_pow_mul_kappa (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) =
      ENNReal.ofReal (r ^ k) * kappa k := by
  rw [MeasureTheory.Measure.addHaar_closedBall' volume 0 hr, finrank_euclideanSpace,
    ← kappa_eq_volume_closedBall]
  simp

/-- The standard orthogonal splitting of `ℝ^(n+1)` into `ℝ^n × ℝ`. -/
def splitFin (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
  let e₁ : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let e₂ : EuclideanSpace ℝ (Fin n ⊕ Fin 1) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)
  e₁.toMeasurableEquiv.trans <|
    e₂.toMeasurableEquiv.trans <|
      (MeasurableEquiv.toLp 2
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))).symm

/-- The standard finite-coordinate splitting preserves Lebesgue volume. -/
theorem splitFin_measurePreserving (n : ℕ) : MeasurePreserving (splitFin n) := by
  let e₁ : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let e₂ : EuclideanSpace ℝ (Fin n ⊕ Fin 1) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)
  have h₁ : MeasurePreserving e₁.toMeasurableEquiv volume volume :=
    LinearIsometryEquiv.measurePreserving e₁
  have h₂ : MeasurePreserving e₂.toMeasurableEquiv volume volume :=
    LinearIsometryEquiv.measurePreserving e₂
  have h₃ : MeasurePreserving
      (MeasurableEquiv.toLp 2
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))).symm volume volume :=
    WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin 1))
  simpa [splitFin, e₁, e₂] using h₁.trans (h₂.trans h₃)

/-- Pythagoras for the standard splitting. -/
theorem splitFin_norm_sq (n : ℕ) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖q‖ ^ 2 = ‖(splitFin n q).1‖ ^ 2 + ‖(splitFin n q).2‖ ^ 2 := by
  let e₁ : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let e₂ : EuclideanSpace ℝ (Fin n ⊕ Fin 1) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)
  have hsplit : splitFin n q = WithLp.ofLp (e₂ (e₁ q)) := by
    rfl
  rw [hsplit]
  calc
    ‖q‖ ^ 2 = ‖e₂ (e₁ q)‖ ^ 2 := by rw [e₂.norm_map, e₁.norm_map]
    _ = ‖(WithLp.ofLp (e₂ (e₁ q))).1‖ ^ 2 +
        ‖(WithLp.ofLp (e₂ (e₁ q))).2‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 (e₂ (e₁ q))

/-- The volume of the one-dimensional unit ball is two. -/
@[simp]
theorem kappa_one : kappa 1 = 2 := by
  rw [kappa_eq_volume_closedBall, EuclideanSpace.volume_closedBall]
  norm_num
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']

@[simp]
theorem kappaReal_one : kappaReal 1 = 2 := by
  simp [kappaReal]

/-- Radius of the base of the cylinder used in dimension `n + 1`. -/
def cylinderRadius (n : ℕ) : ℝ :=
  1 - 1 / (2 * (n + 1 : ℝ))

/-- Half-height of the cylinder used in dimension `n + 1`. -/
def cylinderHalfHeight (n : ℕ) : ℝ :=
  1 / (2 * Real.sqrt (n + 1 : ℝ))

/-- The product cylinder in the orthogonal splitting of dimension `n + 1`. -/
def ballCylinder (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
  closedBall 0 (cylinderRadius n) ×ˢ closedBall 0 (cylinderHalfHeight n)

theorem cylinderRadius_nonneg (n : ℕ) : 0 ≤ cylinderRadius n := by
  have hJ : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hden : 0 < 2 * (n + 1 : ℝ) := by positivity
  have hfrac : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith
  exact sub_nonneg.2 hfrac

theorem cylinderHalfHeight_pos (n : ℕ) : 0 < cylinderHalfHeight n := by
  unfold cylinderHalfHeight
  positivity

theorem cylinderHalfHeight_nonneg (n : ℕ) : 0 ≤ cylinderHalfHeight n :=
  (cylinderHalfHeight_pos n).le

/-- Elementary Bernoulli inequality in the form used for the cylinder base. -/
theorem one_sub_mul_le_pow (n : ℕ) {x : ℝ} (hx1 : x ≤ 1) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hone : 0 ≤ 1 - x := sub_nonneg.2 hx1
      have hfirst :
          1 - ((n + 1 : ℕ) : ℝ) * x ≤ (1 - (n : ℝ) * x) * (1 - x) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        push_cast
        nlinarith [mul_nonneg hn (sq_nonneg x)]
      calc
        1 - ((n + 1 : ℕ) : ℝ) * x ≤ (1 - (n : ℝ) * x) * (1 - x) := hfirst
        _ ≤ (1 - x) ^ n * (1 - x) := mul_le_mul_of_nonneg_right ih hone
        _ = (1 - x) ^ (n + 1) := by rw [pow_succ]

/-- The chosen base radius and half-height fit inside the unit ball. -/
theorem cylinder_radii_sq_le_one (n : ℕ) :
    cylinderRadius n ^ 2 + cylinderHalfHeight n ^ 2 ≤ 1 := by
  let J : ℝ := n + 1
  have hJ : 0 < J := by dsimp [J]; positivity
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hs_sq : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ.le
  have hid :
      1 - ((1 - 1 / (2 * J)) ^ 2 + (1 / (2 * Real.sqrt J)) ^ 2) =
        (3 * J - 1) / (4 * J ^ 2) := by
    field_simp [hJ.ne', hs.ne', hs_sq]
    nlinarith [hs_sq]
  have hnonneg : 0 ≤ (3 * J - 1) / (4 * J ^ 2) := by
    apply div_nonneg
    · dsimp [J]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    · positivity
  dsimp [cylinderRadius, cylinderHalfHeight, J]
  nlinarith [hid, hnonneg]

/-- The product cylinder pulls back to a subset of the next-dimensional unit ball. -/
theorem splitFin_preimage_ballCylinder_subset (n : ℕ) :
    (splitFin n : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ⁻¹' ballCylinder n ⊆
      closedBall 0 1 := by
  intro q hq
  change splitFin n q ∈ ballCylinder n at hq
  rcases hq with ⟨hx, hz⟩
  have hxnorm : ‖(splitFin n q).1‖ ≤ cylinderRadius n := by
    simpa [ballCylinder, Metric.mem_closedBall, dist_zero_right] using hx
  have hznorm : ‖(splitFin n q).2‖ ≤ cylinderHalfHeight n := by
    simpa [ballCylinder, Metric.mem_closedBall, dist_zero_right] using hz
  have hxsq : ‖(splitFin n q).1‖ ^ 2 ≤ cylinderRadius n ^ 2 := by
    nlinarith [norm_nonneg (splitFin n q).1, cylinderRadius_nonneg n]
  have hzsq : ‖(splitFin n q).2‖ ^ 2 ≤ cylinderHalfHeight n ^ 2 := by
    nlinarith [norm_nonneg (splitFin n q).2, cylinderHalfHeight_nonneg n]
  have hqsplit := splitFin_norm_sq n q
  have hradii := cylinder_radii_sq_le_one n
  have hqnorm : ‖q‖ ≤ 1 := by
    nlinarith [norm_nonneg q]
  simpa [Metric.mem_closedBall, dist_zero_right] using hqnorm

/-- Product-volume formula for the contained cylinder. -/
theorem volume_ballCylinder (n : ℕ) :
    volume (ballCylinder n) =
      (ENNReal.ofReal (cylinderRadius n ^ n) * kappa n) *
        (ENNReal.ofReal (cylinderHalfHeight n) * kappa 1) := by
  rw [ballCylinder,
    MeasureTheory.Measure.volume_eq_prod (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin 1)),
    MeasureTheory.Measure.prod_prod,
    volume_closedBall_eq_ofReal_pow_mul_kappa n (cylinderRadius_nonneg n),
    volume_closedBall_eq_ofReal_pow_mul_kappa 1 (cylinderHalfHeight_nonneg n)]
  simp

/-- Real-valued form of the cylinder product-volume formula. -/
theorem volume_ballCylinder_toReal (n : ℕ) :
    (volume (ballCylinder n)).toReal =
      cylinderRadius n ^ n * kappaReal n * (2 * cylinderHalfHeight n) := by
  rw [volume_ballCylinder]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (cylinderRadius_nonneg n) n),
    ENNReal.toReal_ofReal (cylinderHalfHeight_nonneg n)]
  simp only [kappaReal, kappa_one, ENNReal.toReal_ofNat]
  ring

/-- The cylinder measure is at most the next-dimensional unit-ball volume. -/
theorem volume_ballCylinder_le_kappa_succ (n : ℕ) :
    volume (ballCylinder n) ≤ kappa (n + 1) := by
  calc
    volume (ballCylinder n) =
        volume ((splitFin n : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ⁻¹'
            ballCylinder n) :=
      (splitFin_measurePreserving n).measure_preimage_equiv (ballCylinder n) |>.symm
    _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      measure_mono (splitFin_preimage_ballCylinder_subset n)
    _ = kappa (n + 1) := (kappa_eq_volume_closedBall (n + 1)).symm

/-- The base-radius factor loses at most a factor two. -/
theorem half_le_cylinderRadius_pow (n : ℕ) :
    (1 : ℝ) / 2 ≤ cylinderRadius n ^ n := by
  let J : ℝ := n + 1
  have hJ : 0 < J := by dsimp [J]; positivity
  have hden : 0 < 2 * J := by positivity
  have hx1 : 1 / (2 * J) ≤ 1 := by
    rw [div_le_one hden]
    dsimp [J]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hbern := one_sub_mul_le_pow n hx1
  have hnfrac : (n : ℝ) / (2 * J) ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hden]
    dsimp [J]
    nlinarith
  have hleft : (1 : ℝ) / 2 ≤ 1 - (n : ℝ) * (1 / (2 * J)) := by
    have heqfrac : (n : ℝ) * (1 / (2 * J)) = (n : ℝ) / (2 * J) := by ring
    rw [heqfrac]
    nlinarith [hnfrac]
  dsimp [cylinderRadius]
  exact hleft.trans hbern

/-- Consecutive real unit-ball volumes satisfy the weak cylinder ratio bound. -/
theorem kappaReal_succ_lower (n : ℕ) :
    kappaReal n / (2 * Real.sqrt (n + 1 : ℝ)) ≤ kappaReal (n + 1) := by
  have hmeasure := volume_ballCylinder_le_kappa_succ n
  have hmeasureReal := ENNReal.toReal_mono (kappa_ne_top (n + 1)) hmeasure
  rw [volume_ballCylinder_toReal] at hmeasureReal
  have hbase := half_le_cylinderRadius_pow n
  have hk : 0 ≤ kappaReal n := kappaReal_nonneg n
  have hh : 0 ≤ 2 * cylinderHalfHeight n := by
    positivity [cylinderHalfHeight_pos n]
  have hlower :
      (1 / 2 : ℝ) * kappaReal n * (2 * cylinderHalfHeight n) ≤
        cylinderRadius n ^ n * kappaReal n * (2 * cylinderHalfHeight n) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase hk) hh
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have heq :
      (1 / 2 : ℝ) * kappaReal n * (2 * cylinderHalfHeight n) =
        kappaReal n / (2 * Real.sqrt (n + 1 : ℝ)) := by
    unfold cylinderHalfHeight
    field_simp [hs.ne']
  rw [heq] at hlower
  exact hlower.trans hmeasureReal

/-- Division form of the consecutive ratio, for every `j ≥ 1`. -/
theorem kappaReal_consecutive_ratio {j : ℕ} (hj : 1 ≤ j) :
    1 / (2 * Real.sqrt (j : ℝ)) ≤ kappaReal j / kappaReal (j - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (zero_lt_one.trans_le hj))
  rw [Nat.succ_sub_one]
  rw [le_div_iff₀ (kappaReal_pos n)]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using kappaReal_succ_lower n

/-- Iteration of the consecutive estimate with a common denominator `R`. -/
theorem kappaReal_div_pow_le_of_sqrt_le (R : ℝ) (hR : 0 < R)
    {k m : ℕ} (hkm : k ≤ m) (hmR : 2 * Real.sqrt (m : ℝ) ≤ R) :
    kappaReal k / R ^ (m - k) ≤ kappaReal m := by
  induction m with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkm
      subst k
      simp
  | succ m ih =>
      by_cases hk : k = m + 1
      · subst k
        simp
      · have hlt : k < m + 1 := lt_of_le_of_ne hkm hk
        have hkm' : k ≤ m := Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hlt)
        have hmcast : (m : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.le_succ m
        have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (m + 1 : ℕ) :=
          Real.sqrt_le_sqrt hmcast
        have hmR' : 2 * Real.sqrt (m : ℝ) ≤ R :=
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)).trans hmR
        have hind := ih hkm' hmR'
        have hden : 0 < 2 * Real.sqrt (m + 1 : ℕ) := by positivity
        have hquot :
            kappaReal m / R ≤
              kappaReal m / (2 * Real.sqrt (m + 1 : ℕ)) := by
          exact div_le_div_of_nonneg_left (kappaReal_nonneg m) hden hmR
        rw [Nat.succ_sub hkm', pow_succ]
        calc
          kappaReal k / (R ^ (m - k) * R) =
              (kappaReal k / R ^ (m - k)) / R := by
                field_simp [hR.ne']
          _ ≤ kappaReal m / R := div_le_div_of_nonneg_right hind hR.le
          _ ≤ kappaReal m / (2 * Real.sqrt (m + 1 : ℕ)) := hquot
          _ ≤ kappaReal (m + 1) := by
            simpa [Nat.cast_add, Nat.cast_one] using kappaReal_succ_lower m

/-- Telescoped ball-volume estimate, in the division form used by the volume potential. -/
theorem kappaReal_div_pow_sqrt_le {k m : ℕ} (hkm : k ≤ m) :
    kappaReal k / (2 * Real.sqrt (m : ℝ)) ^ (m - k) ≤ kappaReal m := by
  by_cases hm : m = 0
  · subst m
    have hk : k = 0 := Nat.eq_zero_of_le_zero hkm
    subst k
    simp
  · apply kappaReal_div_pow_le_of_sqrt_le (2 * Real.sqrt (m : ℝ))
    · positivity
    · exact hkm
    · exact le_rfl

/-- Equivalently, `κ_m / κ_k` loses at most one factor `2√m` per dropped dimension. -/
theorem kappaReal_ratio_lower {k m : ℕ} (hkm : k ≤ m) :
    ((2 * Real.sqrt (m : ℝ)) ^ (m - k))⁻¹ ≤ kappaReal m / kappaReal k := by
  rw [le_div_iff₀ (kappaReal_pos k)]
  simpa [div_eq_mul_inv, mul_comm] using kappaReal_div_pow_sqrt_le hkm

end ZeroOrderBounds
