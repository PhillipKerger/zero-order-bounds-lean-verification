import Mathlib.Analysis.MeanInequalitiesPow

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# The pointwise algebra in the one-dimensional BBL transport proof

For positive slice radii `a` and `b`, the monotone-transport proof of the
one-dimensional Borell--Brascamp--Lieb inequality reduces to the inequality

`1 ≤ ((1-t) a + t b)^q * ((1-t) / a^q + t / b^q)`.

It is precisely Jensen convexity of `x ↦ x⁻q`.  Keeping this elementary step
separate makes the analytic change-of-variables argument easier to audit.
-/

namespace ZeroOrderBounds.AccuracyImprovement

/-- The pointwise inverse-power inequality used after differentiating the
quantile interpolation in the one-dimensional BBL proof. -/
theorem one_le_weightedPower_mul_weightedInvPower
    (q : ℕ) {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) :
    1 ≤ ((1 - t) * a + t * b) ^ q *
      ((1 - t) * (a ^ q)⁻¹ + t * (b ^ q)⁻¹) := by
  have hOneSub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsum : (1 - t) + t = 1 := by ring
  have hconv := (convexOn_zpow (-(q : ℤ))).2 ha hb hOneSub ht0 hsum
  simp only [smul_eq_mul, zpow_neg, zpow_natCast] at hconv
  have hmix : 0 < (1 - t) * a + t * b := by
    rcases eq_or_lt_of_le ht0 with rfl | ht
    · simpa using ha
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hOneSub ha.le) (mul_pos ht hb)
  calc
    1 = ((1 - t) * a + t * b) ^ q *
        (((1 - t) * a + t * b) ^ q)⁻¹ := by
          rw [mul_inv_cancel₀]
          exact pow_ne_zero q hmix.ne'
    _ ≤ ((1 - t) * a + t * b) ^ q *
        ((1 - t) * (a ^ q)⁻¹ + t * (b ^ q)⁻¹) :=
      mul_le_mul_of_nonneg_left hconv (pow_nonneg hmix.le q)

end ZeroOrderBounds.AccuracyImprovement
