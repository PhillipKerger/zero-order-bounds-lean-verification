import ZeroOrderBounds.BallVolumeRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# A good row and a separated pair

This file contains the last two bookkeeping arguments in the resisting-oracle construction.
First, two global budgets force one row to have both small codimension and small entropy.  For the
particular logarithmic loss used by the oracle, this gives the quarter-power lower bound on that
row's normalized volume radius.  Second, an elementary intrinsic-volume comparison turns such a
lower bound into two separated points of the row body.

The budget theorem is deliberately stated for arbitrary nonnegative entropy data and an arbitrary
positive loss scale.  The later specialization takes the entropy to be `-log rho`.
-/

noncomputable section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Metric Set

namespace ZeroOrderBounds

/-- The logarithmic loss scale from one informative oracle step. -/
def entropyScale (m : ℕ) : ℝ :=
  Real.log ((64 / 3 : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ))

/-- Entropy of a positive normalized volume ratio. -/
def rowEntropy (rho : ℝ) : ℝ :=
  -Real.log rho

theorem rowEntropy_nonneg {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1) :
    0 ≤ rowEntropy rho := by
  rw [rowEntropy, neg_nonneg]
  exact Real.log_nonpos hrho.le hrho_one

theorem entropyScale_eq_log_add {m : ℕ} (hm : 0 < m) :
    entropyScale m =
      Real.log (4 / 3 : ℝ) +
        Real.log (16 * (m : ℝ) * Real.sqrt (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  rw [entropyScale, ← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
    (by positivity : (16 * (m : ℝ) * Real.sqrt (m : ℝ)) ≠ 0)]
  congr 1
  ring

theorem entropyScale_pos {m : ℕ} (hm : 2 ≤ m) : 0 < entropyScale m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := by
    rw [Real.le_sqrt (by norm_num)]
    · nlinarith
    · positivity
  have harg : 1 < (64 / 3 : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) := by
    nlinarith
  exact Real.log_pos harg

/-- The oracle loss scale is at most seven logarithms.  The proof actually obtains the stronger
bound with coefficient three once `m ≥ 1000`. -/
theorem entropyScale_le_seven_log {m : ℕ} (hm : 1000 ≤ m) :
    entropyScale m ≤ 7 * Real.log (m : ℝ) := by
  have hmR : (1000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hmRone : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hsqrt : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr hmRone
  have hargpos : 0 < (64 / 3 : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) := by
    positivity
  have hargle :
      (64 / 3 : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    calc
      (64 / 3 : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) ≤
          (m : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith) hmRpos.le)
              (Real.sqrt_nonneg _)
      _ ≤ (m : ℝ) * (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hmRpos.le hmRpos.le)
      _ = (m : ℝ) ^ 3 := by ring
  have hlognonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmRone
  calc
    entropyScale m ≤ Real.log ((m : ℝ) ^ 3) := by
      exact Real.log_le_log hargpos hargle
    _ = 3 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
    _ ≤ 7 * Real.log (m : ℝ) := by nlinarith

/-- Two global `1/1000` budgets force a row below both `1/100` thresholds.  Keeping the
codimension budget in real-cast form avoids premature natural-number division. -/
theorem exists_good_index_of_budgets {m : ℕ} (hm : 1000 ≤ m)
    (c : Fin m → ℕ) (D : Fin m → ℝ) (L : ℝ)
    (hDnonneg : ∀ i, 0 ≤ D i) (hL : 0 < L)
    (hcBudget : 1000 * ∑ i, (c i : ℝ) ≤ (m : ℝ) ^ 2)
    (hDBudget : 1000 * ∑ i, D i ≤ (m : ℝ) ^ 2 * L) :
    ∃ i, 100 * (c i : ℝ) ≤ (m : ℝ) ∧
      100 * D i ≤ (m : ℝ) * L := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hmpos
  by_contra hgood
  push Not at hgood
  have hrow (i : Fin m) :
      (m : ℝ) * L < 100 * ((c i : ℝ) * L + D i) := by
    by_cases hc : 100 * (c i : ℝ) ≤ (m : ℝ)
    · have hD : (m : ℝ) * L < 100 * D i := hgood i hc
      have hcL : 0 ≤ (c i : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL.le
      nlinarith
    · have hc' : (m : ℝ) < 100 * (c i : ℝ) := lt_of_not_ge hc
      have hcL : (m : ℝ) * L < (100 * (c i : ℝ)) * L :=
        mul_lt_mul_of_pos_right hc' hL
      nlinarith [hDnonneg i]
  have hsumRows :
      ∑ i : Fin m, (m : ℝ) * L <
        ∑ i : Fin m, 100 * ((c i : ℝ) * L + D i) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ hrow i
  have hsum :
      (m : ℝ) ^ 2 * L <
        100 * ((∑ i, (c i : ℝ)) * L + ∑ i, D i) := by
    calc
      (m : ℝ) ^ 2 * L = ∑ i : Fin m, (m : ℝ) * L := by
        simp [pow_two, mul_assoc]
      _ < ∑ i : Fin m, 100 * ((c i : ℝ) * L + D i) := hsumRows
      _ = 100 * ((∑ i, (c i : ℝ)) * L + ∑ i, D i) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_mul]
  have hcBudgetL :
      (1000 * ∑ i, (c i : ℝ)) * L ≤ (m : ℝ) ^ 2 * L :=
    mul_le_mul_of_nonneg_right hcBudget hL.le
  have hupper :
      100 * ((∑ i, (c i : ℝ)) * L + ∑ i, D i) <
        (m : ℝ) ^ 2 * L := by
    have hpositive : 0 < (m : ℝ) ^ 2 * L := by positivity
    nlinarith
  exact (not_lt_of_ge hupper.le) hsum

/-- Direct bridge from the round-count form of the oracle potential to
`exists_good_index_of_budgets`. -/
theorem exists_good_index_of_round_budgets {m T : ℕ} (hm : 1000 ≤ m)
    (c : Fin m → ℕ) (D : Fin m → ℝ) (L : ℝ)
    (hDnonneg : ∀ i, 0 ≤ D i) (hL : 0 < L)
    (hcRounds : ∑ i, c i ≤ T)
    (hDRounds : ∑ i, D i ≤ (T : ℝ) * L)
    (horizon : 1000 * T ≤ m ^ 2) :
    ∃ i, 100 * (c i : ℝ) ≤ (m : ℝ) ∧
      100 * D i ≤ (m : ℝ) * L := by
  have horizonR : (1000 : ℝ) * T ≤ (m : ℝ) ^ 2 := by exact_mod_cast horizon
  have hcRoundsR : ∑ i, (c i : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hcRounds
  have hcBudget : 1000 * ∑ i, (c i : ℝ) ≤ (m : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcRoundsR (by norm_num)).trans horizonR
  have hTL : (1000 : ℝ) * T * L ≤ (m : ℝ) ^ 2 * L :=
    mul_le_mul_of_nonneg_right horizonR hL.le
  have hDBudget : 1000 * ∑ i, D i ≤ (m : ℝ) ^ 2 * L := by
    calc
      1000 * ∑ i, D i ≤ 1000 * ((T : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hDRounds (by norm_num)
      _ = (1000 : ℝ) * T * L := by ring
      _ ≤ (m : ℝ) ^ 2 * L := hTL
  exact exists_good_index_of_budgets hm c D L hDnonneg hL hcBudget hDBudget

/-- A small codimension in the `1/100` sense leaves at least `99/100` of the dimensions. -/
theorem dimension_of_good_codimension {m c : ℕ}
    (hc : 100 * (c : ℝ) ≤ (m : ℝ)) :
    c ≤ m / 100 ∧ 99 * m ≤ 100 * (m - c) ∧ (0 < m → 0 < m - c) := by
  have hcNat : 100 * c ≤ m := by exact_mod_cast hc
  have hcDiv : c ≤ m / 100 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  constructor
  · exact hcDiv
  constructor
  · omega
  · intro hm
    omega

/-- The good row's entropy per surviving dimension is at most `L/99`. -/
theorem entropy_per_dimension_of_good {m c : ℕ} {D L : ℝ}
    (hL : 0 ≤ L)
    (hc : 99 * m ≤ 100 * (m - c))
    (hentropy : 100 * D ≤ (m : ℝ) * L) :
    99 * D ≤ (m - c : ℕ) * L := by
  have hcR : 99 * (m : ℝ) ≤ 100 * (m - c : ℕ) := by exact_mod_cast hc
  have hcRL : (99 * (m : ℝ)) * L ≤ (100 * (m - c : ℕ)) * L :=
    mul_le_mul_of_nonneg_right hcR hL
  nlinarith

/-- Entropy bounded by one quarter of `k log m` gives the power-form radius estimate. -/
theorem rho_lower_quarter_power {m k : ℕ} {rho D : ℝ}
    (hm : 0 < m) (hrho : 0 < rho) (hD : D = rowEntropy rho)
    (hquarter : 4 * D ≤ (k : ℝ) * Real.log (m : ℝ)) :
    (m : ℝ) ^ (-(k : ℝ) / 4) ≤ rho := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogrho : Real.log rho = -D := by
    rw [hD, rowEntropy]
    ring
  rw [Real.rpow_def_of_pos hmR, ← Real.exp_log hrho]
  apply Real.exp_le_exp.mpr
  rw [hlogrho]
  nlinarith

/-- Root form of `rho_lower_quarter_power`. -/
theorem normalized_radius_lower_quarter {m k : ℕ} {rho : ℝ}
    (hm : 0 < m) (hk : 0 < k)
    (hpower : (m : ℝ) ^ (-(k : ℝ) / 4) ≤ rho) :
    (m : ℝ) ^ (-(1 : ℝ) / 4) ≤ rho ^ ((k : ℝ)⁻¹) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hmR.le _) hpower (inv_nonneg.2 hkR.le)
  calc
    (m : ℝ) ^ (-(1 : ℝ) / 4) =
        ((m : ℝ) ^ (-(k : ℝ) / 4)) ^ ((k : ℝ)⁻¹) := by
      rw [← Real.rpow_mul hmR.le]
      congr 1
      field_simp [hkR.ne']
    _ ≤ rho ^ ((k : ℝ)⁻¹) := hroot

/-- Complete numerical good-row theorem for the oracle's actual entropy scale. -/
theorem exists_good_row_quarter_radius {m : ℕ} (hm : 1000 ≤ m)
    (c : Fin m → ℕ) (rho : Fin m → ℝ)
    (hrho_pos : ∀ i, 0 < rho i) (hrho_one : ∀ i, rho i ≤ 1)
    (hcBudget : 1000 * ∑ i, (c i : ℝ) ≤ (m : ℝ) ^ 2)
    (hEntropyBudget :
      1000 * ∑ i, rowEntropy (rho i) ≤ (m : ℝ) ^ 2 * entropyScale m) :
    ∃ i, c i ≤ m / 100 ∧
      99 * m ≤ 100 * (m - c i) ∧
      100 * rowEntropy (rho i) ≤ (m : ℝ) * entropyScale m ∧
      (m : ℝ) ^ (-(m - c i : ℕ) / 4 : ℝ) ≤ rho i ∧
      (m : ℝ) ^ (-(1 : ℝ) / 4) ≤
        rho i ^ (((m - c i : ℕ) : ℝ)⁻¹) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hLpos : 0 < entropyScale m := entropyScale_pos (by omega)
  obtain ⟨i, hci, hDi⟩ := exists_good_index_of_budgets hm c
    (fun i ↦ rowEntropy (rho i)) (entropyScale m)
    (fun i ↦ rowEntropy_nonneg (hrho_pos i) (hrho_one i)) hLpos hcBudget hEntropyBudget
  obtain ⟨hcdiv, hdim, hkpos⟩ := dimension_of_good_codimension hci
  have hk : 0 < m - c i := hkpos hmpos
  have hper := entropy_per_dimension_of_good
    hLpos.le hdim hDi
  have hLseven := entropyScale_le_seven_log hm
  have hkR : (0 : ℝ) ≤ ((m - c i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hscaled :
      (m - c i : ℕ) * entropyScale m ≤
        (m - c i : ℕ) * (7 * Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hLseven hkR
  have hlognonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hquarter :
      4 * rowEntropy (rho i) ≤
        (m - c i : ℕ) * Real.log (m : ℝ) := by
    nlinarith
  have hpower := rho_lower_quarter_power hmpos (hrho_pos i) rfl hquarter
  have hroot := normalized_radius_lower_quarter hmpos hk hpower
  exact ⟨i, hcdiv, hdim, hDi, hpower, hroot⟩

section SeparatedPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If a body's real intrinsic volume is larger than that of a radius-`r` ball in its affine
dimension, the body contains two points at distance at least `r`. -/
theorem IntrinsicBody.exists_pair_dist_ge_of_ball_volume_lt (P : IntrinsicBody E)
    {r : ℝ} (hr : 0 ≤ r)
    (hlarge : r ^ P.dim * kappaReal P.dim < P.volumeReal) :
    ∃ x ∈ P.carrier, ∃ y ∈ P.carrier, r ≤ dist x y := by
  by_contra hpairs
  push Not at hpairs
  have hvolume := P.volume_le_of_pairwise_dist_lt hpairs
  have htop : ENNReal.ofReal r ^ P.dim * kappa P.dim ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (kappa_ne_top P.dim)
  have hreal := ENNReal.toReal_mono htop hvolume
  have hbound : P.volumeReal ≤ r ^ P.dim * kappaReal P.dim := by
    simpa [IntrinsicBody.volume, IntrinsicBody.volumeReal, intrinsicVolumeReal,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, kappaReal] using hreal
  exact (not_lt_of_ge hbound) hlarge

/-- Separated-pair theorem in normalized-volume form. -/
theorem IntrinsicBody.exists_pair_dist_ge_of_volume_normalization (P : IntrinsicBody E)
    {tau rho r : ℝ} (hr : 0 ≤ r)
    (hvolume : P.volumeReal = kappaReal P.dim * tau ^ P.dim * rho)
    (hscale : r ^ P.dim < tau ^ P.dim * rho) :
    ∃ x ∈ P.carrier, ∃ y ∈ P.carrier, r ≤ dist x y := by
  apply P.exists_pair_dist_ge_of_ball_volume_lt hr
  rw [hvolume]
  have hmul := mul_lt_mul_of_pos_right hscale (kappaReal_pos P.dim)
  nlinarith

/-- Quarter-power specialization used for the final good row. -/
theorem IntrinsicBody.exists_pair_dist_ge_quarter (P : IntrinsicBody E)
    {m : ℕ} {tau rho : ℝ} (hm : 0 < m) (hdim : 0 < P.dim)
    (htau : 0 < tau)
    (hvolume : P.volumeReal = kappaReal P.dim * tau ^ P.dim * rho)
    (hrhoPower : (m : ℝ) ^ (-(P.dim : ℝ) / 4) ≤ rho) :
    ∃ x ∈ P.carrier, ∃ y ∈ P.carrier,
      tau / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4) ≤ dist x y := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hxpow : 0 < (m : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hmR _
  have hpowEq :
      ((m : ℝ) ^ (-(1 : ℝ) / 4)) ^ P.dim =
        (m : ℝ) ^ (-(P.dim : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    congr 1
    ring
  have hhalf : (1 / 2 : ℝ) ^ P.dim < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hdim.ne'
  have hxpowK : 0 < (m : ℝ) ^ (-(P.dim : ℝ) / 4) :=
    Real.rpow_pos_of_pos hmR _
  have hstrict :
      (tau / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4)) ^ P.dim <
        tau ^ P.dim * (m : ℝ) ^ (-(P.dim : ℝ) / 4) := by
    rw [show tau / 2 = tau * (1 / 2 : ℝ) by ring, mul_pow, mul_pow, hpowEq]
    have hleft : tau ^ P.dim * (1 / 2 : ℝ) ^ P.dim < tau ^ P.dim :=
      by simpa using mul_lt_mul_of_pos_left hhalf (pow_pos htau P.dim)
    have h := mul_lt_mul_of_pos_right hleft hxpowK
    simpa [mul_assoc] using h
  have hscale :
      (tau / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4)) ^ P.dim <
        tau ^ P.dim * rho := by
    exact hstrict.trans_le
      (mul_le_mul_of_nonneg_left hrhoPower (pow_nonneg htau.le P.dim))
  exact P.exists_pair_dist_ge_of_volume_normalization
    (mul_nonneg (div_nonneg htau.le (by norm_num)) hxpow.le) hvolume hscale

end SeparatedPair

end ZeroOrderBounds
