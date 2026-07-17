import FullDMinusOneHalfAccuracy.BorellBrascampLiebAlgebra
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# The smooth-transport core of one-dimensional BBL

The dimension-induction proof of Brunn--Minkowski reduces its analytic step
to a one-dimensional Borell--Brascamp--Lieb inequality for slice volumes.
This file proves the complete change-of-variables part of that argument under
an explicit smooth monotone-transport certificate.

If `T` transports the density `f` to `g`, then

`g (T x) * T' x = f x`.

For the interpolated coordinate `z x = (1-t) x + t T x`, the pointwise
slice inequality and weighted AM--GM imply

`f x ≤ h (z x) * z' x`.

Integration and Mathlib's one-dimensional substitution theorem then give
the desired BBL integral inequality.  No BBL or Brunn--Minkowski assertion is
assumed in this module.

The remaining analytic task for the convex-body proof is to build `T` from
the normalized CDFs of the two positive interior slice densities.  The
intended construction is `T = G⁻¹ ∘ F`, first on compact subintervals of
the interiors of their supports and then by a monotone limit to the support
endpoints.
-/

noncomputable section

open Real
open scoped Interval

namespace ZeroOrderBounds.AccuracyImprovement

/-- Pointwise Jacobian inequality in the BBL transport proof.  Here `p` is
the dimension of a codimension-one slice, `a` and `b` are its two slice
volumes, and `c` is the derivative of the mass transport. -/
theorem bbl_transport_jacobian_bound {p : ℕ} (hp : 0 < p)
    {t a b c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hbc : b * c = a) :
    a ≤
      (((1 - t) * a ^ ((p : ℝ)⁻¹) + t * b ^ ((p : ℝ)⁻¹)) ^ (p : ℝ)) *
        ((1 - t) + t * c) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hwt : (1 - t) + t = 1 := by ring
  let A : ℝ := (1 - t) * a ^ ((p : ℝ)⁻¹) + t * b ^ ((p : ℝ)⁻¹)
  let B : ℝ := (1 - t) + t * c
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAMGA :
      ((a ^ ((p : ℝ)⁻¹)) ^ (1 - t)) *
        ((b ^ ((p : ℝ)⁻¹)) ^ t) ≤ A := by
    simpa [A] using Real.geom_mean_le_arith_mean2_weighted
      (p₁ := a ^ ((p : ℝ)⁻¹)) (p₂ := b ^ ((p : ℝ)⁻¹))
      (sub_nonneg.mpr ht1) ht0
      (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _) hwt
  have hA :
      a ^ (((p : ℝ)⁻¹ * (1 - t)) * (p : ℝ)) *
          b ^ (((p : ℝ)⁻¹ * t) * (p : ℝ)) ≤ A ^ (p : ℝ) := by
    let X : ℝ := ((a ^ ((p : ℝ)⁻¹)) ^ (1 - t)) *
      ((b ^ ((p : ℝ)⁻¹)) ^ t)
    have hX0 : 0 ≤ X := by dsimp [X]; positivity
    have hXA : X ≤ A := by simpa [X] using hAMGA
    have hpow : X ^ (p : ℝ) ≤ A ^ (p : ℝ) :=
      Real.rpow_le_rpow hX0 hXA hpR.le
    dsimp [X, A] at hpow ⊢
    rw [Real.mul_rpow
          (Real.rpow_nonneg (Real.rpow_nonneg ha.le _) _)
          (Real.rpow_nonneg (Real.rpow_nonneg hb.le _) _),
      ← Real.rpow_mul (Real.rpow_nonneg ha.le _),
      ← Real.rpow_mul (Real.rpow_nonneg hb.le _),
      ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le] at hpow
    convert hpow using 1 <;> ring
  have hAMGB : c ^ t ≤ B := by
    have h := Real.geom_mean_le_arith_mean2_weighted
      (sub_nonneg.mpr ht1) ht0 (by positivity : (0 : ℝ) ≤ 1) hc hwt
    simpa [B] using h
  have hexpa : ((p : ℝ)⁻¹ * (1 - t)) * (p : ℝ) = 1 - t := by
    field_simp
  have hexpb : ((p : ℝ)⁻¹ * t) * (p : ℝ) = t := by
    field_simp
  rw [hexpa, hexpb] at hA
  calc
    a = a ^ (1 - t) * a ^ t := by
      rw [← Real.rpow_add ha]
      norm_num
    _ = a ^ (1 - t) * (b * c) ^ t := by rw [hbc]
    _ = (a ^ (1 - t) * b ^ t) * c ^ t := by
      rw [Real.mul_rpow hb.le hc]
      ring
    _ ≤ A ^ (p : ℝ) * B :=
      mul_le_mul hA hAMGB (Real.rpow_nonneg hc _)
        (Real.rpow_nonneg hA0 _)
    _ = _ := by rfl

/-- The interpolated line coordinate in monotone transport. -/
def bblInterpolatedCoordinate (t : ℝ) (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - t) * x + t * T x

/-- Its expected derivative when `T'` is the derivative of `T`. -/
def bblInterpolatedJacobian (t : ℝ) (T' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - t) + t * T' x

theorem hasDerivAt_bblInterpolatedCoordinate
    {t : ℝ} {T T' : ℝ → ℝ} {x : ℝ}
    (hT : HasDerivAt T (T' x) x) :
    HasDerivAt (bblInterpolatedCoordinate t T)
      (bblInterpolatedJacobian t T' x) x := by
  have h := (hasDerivAt_id x).const_mul (1 - t) |>.add (hT.const_mul t)
  change HasDerivAt (fun y : ℝ ↦ (1 - t) * y + t * T y)
    ((1 - t) + t * T' x) x
  have hfun :
      ((fun y : ℝ ↦ (1 - t) * id y) + (fun y : ℝ ↦ t * T y)) =
        (fun y : ℝ ↦ (1 - t) * y + t * T y) := by
    funext y
    rfl
  rw [← hfun]
  simpa only [mul_one] using h

/-- The pointwise BBL conclusion after combining the slice inequality with
the transport identity. -/
theorem bbl_pointwise_of_transport
    {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {f g h T T' : ℝ → ℝ} {x : ℝ}
    (hf : 0 < f x) (hg : 0 < g (T x)) (hT' : 0 ≤ T' x)
    (hmass : g (T x) * T' x = f x)
    (hsection :
      (((1 - t) * (f x) ^ ((p : ℝ)⁻¹) +
        t * (g (T x)) ^ ((p : ℝ)⁻¹)) ^ (p : ℝ)) ≤
          h (bblInterpolatedCoordinate t T x)) :
    f x ≤ h (bblInterpolatedCoordinate t T x) *
      bblInterpolatedJacobian t T' x := by
  have hjac : 0 ≤ bblInterpolatedJacobian t T' x := by
    dsimp [bblInterpolatedJacobian]
    positivity
  calc
    f x ≤
        (((1 - t) * (f x) ^ ((p : ℝ)⁻¹) +
          t * (g (T x)) ^ ((p : ℝ)⁻¹)) ^ (p : ℝ)) *
            bblInterpolatedJacobian t T' x := by
      exact bbl_transport_jacobian_bound hp ht0 ht1 hf hg hT' hmass
    _ ≤ h (bblInterpolatedCoordinate t T x) *
          bblInterpolatedJacobian t T' x :=
      mul_le_mul_of_nonneg_right hsection hjac

/-- Finite-interval BBL for an explicit smooth mass transport.

This is the exact analytic endpoint needed after the convex-body slicing
argument supplies `hsection`.  All hypotheses are proof-relevant analytic
certificates; in particular, the existence of `T` is not hidden in a
typeclass or an axiom.
-/
theorem bbl_interval_of_smooth_transport
    {p : ℕ} (hp : 0 < p) {t a b : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hab : a ≤ b)
    {f g h T T' : ℝ → ℝ}
    (hTcont : ContinuousOn T (Set.Icc a b))
    (hTderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt T (T' x) x)
    (hT'nonneg : ∀ x ∈ Set.Ioo a b, 0 ≤ T' x)
    (hfpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    (hgpos : ∀ x ∈ Set.Ioo a b, 0 < g (T x))
    (hmass : ∀ x ∈ Set.Ioo a b, g (T x) * T' x = f x)
    (hsection : ∀ x ∈ Set.Ioo a b,
      (((1 - t) * (f x) ^ ((p : ℝ)⁻¹) +
        t * (g (T x)) ^ ((p : ℝ)⁻¹)) ^ (p : ℝ)) ≤
          h (bblInterpolatedCoordinate t T x))
    (hfint : IntervalIntegrable f MeasureTheory.volume a b)
    (htransint : IntervalIntegrable
      (fun x ↦ h (bblInterpolatedCoordinate t T x) *
        bblInterpolatedJacobian t T' x) MeasureTheory.volume a b) :
    (∫ x in a..b, f x) ≤
      ∫ u in (bblInterpolatedCoordinate t T a)..
        (bblInterpolatedCoordinate t T b), h u := by
  have hzcont : ContinuousOn (bblInterpolatedCoordinate t T) [[a, b]] := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.add
    · exact continuousOn_const.mul continuousOn_id
    · exact continuousOn_const.mul hTcont
  have hzderiv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (bblInterpolatedCoordinate t T)
        (bblInterpolatedJacobian t T' x) x := by
    rw [min_eq_left hab, max_eq_right hab]
    intro x hx
    exact hasDerivAt_bblInterpolatedCoordinate (hTderiv x hx)
  have hz'nonneg : ∀ x ∈ Set.Ioo (min a b) (max a b),
      0 ≤ bblInterpolatedJacobian t T' x := by
    rw [min_eq_left hab, max_eq_right hab]
    intro x hx
    dsimp [bblInterpolatedJacobian]
    have hx' := hT'nonneg x hx
    positivity
  calc
    (∫ x in a..b, f x) ≤
        ∫ x in a..b, h (bblInterpolatedCoordinate t T x) *
          bblInterpolatedJacobian t T' x := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab hfint htransint
      intro x hx
      exact bbl_pointwise_of_transport hp ht0 ht1
        (hfpos x hx) (hgpos x hx) (hT'nonneg x hx)
        (hmass x hx) (hsection x hx)
    _ = ∫ u in (bblInterpolatedCoordinate t T a)..
          (bblInterpolatedCoordinate t T b), h u := by
      exact intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        hzcont hzderiv hz'nonneg

end ZeroOrderBounds.AccuracyImprovement
