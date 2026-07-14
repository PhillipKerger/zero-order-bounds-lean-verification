import ZeroOrderBounds.ProjectionGeometry
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# From separated optimizers to an objective gap

These elementary lemmas are the final analytic bridge in the lower-bound
argument.  They are independent of the resisting oracle: two transcript-
compatible instances have a common algorithmic output, while their unique
optimizers are separated.  The triangle inequality makes the output far from
one optimizer, and the quadratic growth theorem converts that distance into
objective error.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds

/-- Any third point is at least half the mutual distance from one of two points. -/
theorem half_dist_le_dist_or_dist {X : Type*} [PseudoMetricSpace X]
    (x y z : X) :
    dist x y / 2 ≤ dist z x ∨ dist x y / 2 ≤ dist z y := by
  by_contra h
  push Not at h
  have htri := dist_triangle x z y
  rw [dist_comm x z] at htri
  linarith

/-- Growth with the uniform lower bound `a / sqrt m` on the minimum point. -/
theorem hardObjective_growth_uniform {m : ℕ} [NeZero m]
    (W : RowMatrix m) {q : QuerySpace m} (hq : q ∈ unitBall m) :
    a / (2 * Real.sqrt (m : ℝ)) * ‖q - hardOptimizer W‖ ^ 2 ≤
      hardObjective W q - hardObjective W (hardOptimizer W) := by
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hp := a_div_sqrt_le_norm_minPoint W
  have hsquare : 0 ≤ ‖q - hardOptimizer W‖ ^ 2 := sq_nonneg _
  calc
    a / (2 * Real.sqrt (m : ℝ)) * ‖q - hardOptimizer W‖ ^ 2 =
        (a / Real.sqrt (m : ℝ)) / 2 *
          ‖q - hardOptimizer W‖ ^ 2 := by ring
    _ ≤ ‖minPoint W‖ / 2 * ‖q - hardOptimizer W‖ ^ 2 := by
      gcongr
    _ ≤ hardObjective W q - hardObjective W (hardOptimizer W) :=
      hardObjective_growth W hq

/-- If two hard optimizers are `delta` apart, a common unit-ball output incurs
the stated quadratic gap on at least one of the two objectives. -/
theorem one_of_two_objective_gaps {m : ℕ} [NeZero m]
    (W W' : RowMatrix m) {q : QuerySpace m} (hq : q ∈ unitBall m)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ ‖hardOptimizer W - hardOptimizer W'‖) :
    a / (8 * Real.sqrt (m : ℝ)) * delta ^ 2 ≤
        hardObjective W q - hardObjective W (hardOptimizer W) ∨
      a / (8 * Real.sqrt (m : ℝ)) * delta ^ 2 ≤
        hardObjective W' q - hardObjective W' (hardOptimizer W') := by
  have hfar := half_dist_le_dist_or_dist
    (hardOptimizer W) (hardOptimizer W') q
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hfar
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hcoeff : 0 ≤ a / (2 * Real.sqrt (m : ℝ)) :=
    div_nonneg a_pos.le (mul_nonneg (by norm_num) hsqrt.le)
  rcases hfar with hWfar | hW'far
  · left
    have hdist : delta / 2 ≤ ‖q - hardOptimizer W‖ :=
      (div_le_div_of_nonneg_right hdelta (by norm_num)).trans hWfar
    have hsq : (delta / 2) ^ 2 ≤ ‖q - hardOptimizer W‖ ^ 2 := by
      nlinarith [norm_nonneg (q - hardOptimizer W)]
    calc
      a / (8 * Real.sqrt (m : ℝ)) * delta ^ 2 =
          a / (2 * Real.sqrt (m : ℝ)) * (delta / 2) ^ 2 := by ring
      _ ≤ a / (2 * Real.sqrt (m : ℝ)) *
          ‖q - hardOptimizer W‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoeff
      _ ≤ hardObjective W q - hardObjective W (hardOptimizer W) :=
        hardObjective_growth_uniform W hq
  · right
    have hdist : delta / 2 ≤ ‖q - hardOptimizer W'‖ :=
      (div_le_div_of_nonneg_right hdelta (by norm_num)).trans hW'far
    have hsq : (delta / 2) ^ 2 ≤ ‖q - hardOptimizer W'‖ ^ 2 := by
      nlinarith [norm_nonneg (q - hardOptimizer W')]
    calc
      a / (8 * Real.sqrt (m : ℝ)) * delta ^ 2 =
          a / (2 * Real.sqrt (m : ℝ)) * (delta / 2) ^ 2 := by ring
      _ ≤ a / (2 * Real.sqrt (m : ℝ)) *
          ‖q - hardOptimizer W'‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoeff
      _ ≤ hardObjective W' q - hardObjective W' (hardOptimizer W') :=
        hardObjective_growth_uniform W' hq

/-- Convenient specialization to the separation scale supplied by the
one-row sensitivity theorem. -/
theorem one_of_two_objective_gaps_of_sensitivity_scale {m : ℕ} [NeZero m]
    (W W' : RowMatrix m) {q : QuerySpace m} (hq : q ∈ unitBall m)
    {H : ℝ} (hH : 0 ≤ H)
    (hsep : H / (16 * a * Real.sqrt (m : ℝ)) ≤
      ‖hardOptimizer W - hardOptimizer W'‖) :
    H ^ 2 / (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) ≤
        hardObjective W q - hardObjective W (hardOptimizer W) ∨
      H ^ 2 / (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) ≤
        hardObjective W' q - hardObjective W' (hardOptimizer W') := by
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hdelta0 : 0 ≤ H / (16 * a * Real.sqrt (m : ℝ)) := by
    exact div_nonneg hH
      (mul_nonneg (mul_nonneg (by norm_num) a_pos.le) hs.le)
  have hor := one_of_two_objective_gaps W W' hq hdelta0 hsep
  have heq :
      a / (8 * Real.sqrt (m : ℝ)) *
          (H / (16 * a * Real.sqrt (m : ℝ))) ^ 2 =
        H ^ 2 / (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) := by
    have ha : a ≠ 0 := a_pos.ne'
    have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
    field_simp [ha, hs.ne']
    nlinarith
  rw [heq] at hor
  exact hor

/-- The quarter-power row separation makes the symbolic sensitivity-scale gap
strictly larger than the advertised `1 / (200000000 m³)` constant. -/
theorem quarter_separation_gap_gt_advertised {m : ℕ} [NeZero m]
    {H : ℝ}
    (hH : tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4) ≤ H) :
    1 / (200000000 * (m : ℝ) ^ 3) <
      H ^ 2 / (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) := by
  have hmNat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmNat
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm.le
  have hrpow : 0 < (m : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hm _
  have hrootIdentity :
      ((m : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * Real.sqrt (m : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le, Real.sqrt_eq_rpow,
      ← Real.rpow_add hm]
    norm_num
  have hr : 0 < tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4) := by
    exact mul_pos (div_pos (tau_pos hmNat) (by norm_num)) hrpow
  have hHnonneg : 0 ≤ H := hr.le.trans hH
  have hsq :
      (tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 ≤ H ^ 2 := by
    nlinarith
  have hden : 0 < 2048 * a * (m : ℝ) * Real.sqrt (m : ℝ) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) a_pos) hm) hs
  have hscale :
      (tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 /
          (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) ≤
        H ^ 2 / (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) :=
    div_le_div_of_nonneg_right hsq hden.le
  have heval :
      (tau m / 2 * (m : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 /
          (2048 * a * (m : ℝ) * Real.sqrt (m : ℝ)) =
        a / (8192 * Gamma ^ 2 * (m : ℝ) ^ 3) := by
    rw [tau]
    have ha : a ≠ 0 := a_pos.ne'
    have hG : Gamma ≠ 0 := Gamma_pos.ne'
    field_simp [ha, hG, hs.ne']
    nlinarith
  have hconstant :
      1 / (200000000 * (m : ℝ) ^ 3) <
        a / (8192 * Gamma ^ 2 * (m : ℝ) ^ 3) := by
    have hx3 : 0 < (m : ℝ) ^ 3 := pow_pos hm _
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hx3)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Gamma_pos)) hx3)]
    norm_num [a, Gamma]
    nlinarith
  rw [← heval] at hconstant
  exact hconstant.trans_le hscale

end ZeroOrderBounds
