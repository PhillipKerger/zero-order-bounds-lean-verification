import FullDMinusOneHalfAccuracy.BBLIntegrableTransport
import FullDMinusOneHalfAccuracy.BrunnMinkowskiReduction
import FullDMinusOneHalfAccuracy.BrunnMinkowskiSliceProfiles
import FullDMinusOneHalfAccuracy.BrunnMinkowskiTransport
import FullDMinusOneHalfAccuracy.SliceProfilePositivity
import FullDMinusOneHalfAccuracy.SliceProjectionPositive

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Brunn--Minkowski induction step in a product space

This module combines the geometric slice profiles with the endpoint-robust
one-dimensional BBL theorem.  The principal result first treats bodies of
real volume one in `ℝ × V`; a short wrapper then gives the equal-root case
needed by the general positive-volume normalization.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ZeroOrderBounds.AccuracyImprovement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The two interpolated projection endpoints are themselves attained by
slices of the weighted Minkowski sum. -/
theorem weighted_projection_endpoints_nonempty
    (K L : ConvexBody (ℝ × V)) (t : ℝ) :
    (verticalSlice ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) : Set (ℝ × V))
      ((1 - t) * sliceLeftEndpoint K + t * sliceLeftEndpoint L)).Nonempty ∧
    (verticalSlice ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) : Set (ℝ × V))
      ((1 - t) * sliceRightEndpoint K + t * sliceRightEndpoint L)).Nonempty := by
  have hKleft := (verticalSlice_nonempty_iff_mem_Icc K (sliceLeftEndpoint K)).2
    (left_mem_Icc.mpr (sliceLeftEndpoint_le_sliceRightEndpoint K))
  have hLleft := (verticalSlice_nonempty_iff_mem_Icc L (sliceLeftEndpoint L)).2
    (left_mem_Icc.mpr (sliceLeftEndpoint_le_sliceRightEndpoint L))
  have hKright := (verticalSlice_nonempty_iff_mem_Icc K (sliceRightEndpoint K)).2
    (right_mem_Icc.mpr (sliceLeftEndpoint_le_sliceRightEndpoint K))
  have hLright := (verticalSlice_nonempty_iff_mem_Icc L (sliceRightEndpoint L)).2
    (right_mem_Icc.mpr (sliceLeftEndpoint_le_sliceRightEndpoint L))
  constructor
  · exact (weightedMinkowski t
      (verticalSliceBody K (sliceLeftEndpoint K) hKleft)
      (verticalSliceBody L (sliceLeftEndpoint L) hLleft)).nonempty.mono
        (weighted_verticalSliceBody_subset K L hKleft hLleft)
  · exact (weightedMinkowski t
      (verticalSliceBody K (sliceRightEndpoint K) hKright)
      (verticalSliceBody L (sliceRightEndpoint L) hLright)).nonempty.mono
        (weighted_verticalSliceBody_subset K L hKright hLright)

/-- The induction step at the normalized volume-one level. -/
theorem one_le_volumeReal_weightedMinkowski_of_volumeReal_one
    (hBM : ∀ (s : ℝ) (A B : ConvexBody V),
      0 ≤ s → s ≤ 1 → BrunnMinkowskiAt s A B)
    (hdim : Module.finrank ℝ V ≠ 0)
    (K L : ConvexBody (ℝ × V)) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hKvol : (volume (K : Set (ℝ × V))).toReal = 1)
    (hLvol : (volume (L : Set (ℝ × V))).toReal = 1) :
    1 ≤ (volume ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal := by
  let q : ℕ := Module.finrank ℝ V
  let M : ConvexBody (ℝ × V) := (1 - t) • K + t • L
  have hKvolPos : 0 < (volume (K : Set (ℝ × V))).toReal := by
    rw [hKvol]
    norm_num
  have hLvolPos : 0 < (volume (L : Set (ℝ × V))).toReal := by
    rw [hLvol]
    norm_num
  have hKmeasurePos : 0 < volume (K : Set (ℝ × V)) :=
    (ENNReal.toReal_pos_iff.mp hKvolPos).1
  have hLmeasurePos : 0 < volume (L : Set (ℝ × V)) :=
    (ENNReal.toReal_pos_iff.mp hLvolPos).1
  have hKend : sliceLeftEndpoint K < sliceRightEndpoint K :=
    sliceLeftEndpoint_lt_sliceRightEndpoint_of_volume_pos K hKmeasurePos
  have hLend : sliceLeftEndpoint L < sliceRightEndpoint L :=
    sliceLeftEndpoint_lt_sliceRightEndpoint_of_volume_pos L hLmeasurePos
  have hKpos : ∀ x ∈ Ioo (sliceLeftEndpoint K) (sliceRightEndpoint K),
      0 < sliceVolumeRadius K x :=
    sliceVolumeRadius_pos_on_Ioo hBM K hKvolPos
  have hLpos : ∀ x ∈ Ioo (sliceLeftEndpoint L) (sliceRightEndpoint L),
      0 < sliceVolumeRadius L x :=
    sliceVolumeRadius_pos_on_Ioo hBM L hLvolPos
  have hKi : IntervalIntegrable
      (fun x ↦ sliceVolumeRadius K x ^ q) volume
      (sliceLeftEndpoint K) (sliceRightEndpoint K) := by
    simpa only [q] using intervalIntegrable_sliceVolumeRadius_pow K hdim
  have hLi : IntervalIntegrable
      (fun x ↦ sliceVolumeRadius L x ^ q) volume
      (sliceLeftEndpoint L) (sliceRightEndpoint L) := by
    simpa only [q] using intervalIntegrable_sliceVolumeRadius_pow L hdim
  have hMi : IntervalIntegrable
      (fun x ↦ sliceVolumeRadius M x ^ q) volume
      ((1 - t) * sliceLeftEndpoint K + t * sliceLeftEndpoint L)
      ((1 - t) * sliceRightEndpoint K + t * sliceRightEndpoint L) := by
    exact (integrable_sliceVolumeRadius_pow M hdim).intervalIntegrable
  have hKnorm :
      (∫ x in sliceLeftEndpoint K..sliceRightEndpoint K,
        sliceVolumeRadius K x ^ q) = 1 := by
    simpa only [q, integral_sliceVolumeRadius_pow_projection K hdim, hKvol]
  have hLnorm :
      (∫ x in sliceLeftEndpoint L..sliceRightEndpoint L,
        sliceVolumeRadius L x ^ q) = 1 := by
    simpa only [q, integral_sliceVolumeRadius_pow_projection L hdim, hLvol]
  have hBBL :
      1 ≤ ∫ x in
        (1 - t) * sliceLeftEndpoint K + t * sliceLeftEndpoint L..
        (1 - t) * sliceRightEndpoint K + t * sliceRightEndpoint L,
        sliceVolumeRadius M x ^ q := by
    apply one_le_integral_of_integrable_quantile_power_lower_bound
      q ht₀ ht₁ hKend hLend hKi hLi
      (continuousOn_sliceVolumeRadius_Ioo hBM K)
      (continuousOn_sliceVolumeRadius_Ioo hBM L) hMi hKpos hLpos hKnorm hLnorm
    intro u hu
    let QK : ℝ → ℝ := integrableDensityQuantile hKend hKi
      (fun x hx ↦ pow_pos (hKpos x hx) q) hKnorm
    let QL : ℝ → ℝ := integrableDensityQuantile hLend hLi
      (fun x hx ↦ pow_pos (hLpos x hx) q) hLnorm
    have hQK : QK u ∈ Ioo (sliceLeftEndpoint K) (sliceRightEndpoint K) :=
      integrableDensityQuantile_mem_Ioo hKend hKi
        (fun x hx ↦ pow_pos (hKpos x hx) q) hKnorm hu
    have hQL : QL u ∈ Ioo (sliceLeftEndpoint L) (sliceRightEndpoint L) :=
      integrableDensityQuantile_mem_Ioo hLend hLi
        (fun x hx ↦ pow_pos (hLpos x hx) q) hLnorm hu
    have hsliceK :
        (verticalSlice (K : Set (ℝ × V)) (QK u)).Nonempty :=
      (verticalSlice_nonempty_iff_mem_Icc K (QK u)).2 ⟨hQK.1.le, hQK.2.le⟩
    have hsliceL :
        (verticalSlice (L : Set (ℝ × V)) (QL u)).Nonempty :=
      (verticalSlice_nonempty_iff_mem_Icc L (QL u)).2 ⟨hQL.1.le, hQL.2.le⟩
    have hroot := weighted_sliceVolumeRadius_le_weightedMinkowski_of_brunnMinkowski
      hBM K L ht₀ ht₁ hsliceK hsliceL
    have hbase : 0 ≤
        (1 - t) * sliceVolumeRadius K (QK u) +
          t * sliceVolumeRadius L (QL u) :=
      add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht₁) (sliceVolumeRadius_nonneg K _))
        (mul_nonneg ht₀ (sliceVolumeRadius_nonneg L _))
    apply pow_le_pow_left₀ hbase hroot q
  let c : ℝ := (1 - t) * sliceLeftEndpoint K + t * sliceLeftEndpoint L
  let d : ℝ := (1 - t) * sliceRightEndpoint K + t * sliceRightEndpoint L
  have hcd : c ≤ d := by
    dsimp only [c, d]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₁)
      (sub_nonneg.mpr (sliceLeftEndpoint_le_sliceRightEndpoint K)),
      mul_nonneg ht₀
        (sub_nonneg.mpr (sliceLeftEndpoint_le_sliceRightEndpoint L))]
  obtain ⟨hcne, hdne⟩ := weighted_projection_endpoints_nonempty K L t
  have hcLeft : sliceLeftEndpoint M ≤ c := by
    exact sliceLeftEndpoint_le M
      ((verticalSlice_nonempty_iff_mem_projection M c).1 hcne)
  have hdRight : d ≤ sliceRightEndpoint M := by
    exact le_sliceRightEndpoint M
      ((verticalSlice_nonempty_iff_mem_projection M d).1 hdne)
  have hIntervalMono :
      (∫ x in c..d, sliceVolumeRadius M x ^ q) ≤
        ∫ x in sliceLeftEndpoint M..sliceRightEndpoint M,
          sliceVolumeRadius M x ^ q := by
    apply intervalIntegral.integral_mono_interval hcLeft hcd hdRight
    · exact Filter.Eventually.of_forall fun x ↦
        pow_nonneg (sliceVolumeRadius_nonneg M x) q
    · simpa only [q] using intervalIntegrable_sliceVolumeRadius_pow M hdim
  calc
    1 ≤ ∫ x in c..d, sliceVolumeRadius M x ^ q := by
      simpa only [c, d] using hBBL
    _ ≤ ∫ x in sliceLeftEndpoint M..sliceRightEndpoint M,
        sliceVolumeRadius M x ^ q := hIntervalMono
    _ = (volume (M : Set (ℝ × V))).toReal := by
      simpa only [q] using integral_sliceVolumeRadius_pow_projection M hdim
    _ = (volume ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal := rfl

/-- Real volume scaling in the plain product model.  This duplicates the
inner-product-space lemma only because the ordinary product norm is not the
L2 norm and hence carries no `InnerProductSpace` instance. -/
theorem productConvexBodyVolumeReal_smul_of_nonneg
    (K : ConvexBody (ℝ × V)) {c : ℝ} (hc : 0 ≤ c) :
    (volume ((c • K : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal =
      c ^ Module.finrank ℝ (ℝ × V) *
        (volume (K : Set (ℝ × V))).toReal := by
  calc
    (volume ((c • K : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal =
        (volume (toLpConvexBody (c • K) : Set (WithLp 2 (ℝ × V)))).toReal := by
      rw [volume_toLpConvexBody]
    _ = convexBodyVolumeReal (c • toLpConvexBody K) := by
      rw [toLpConvexBody, continuousLinearEquivImage_smul]
      rfl
    _ = c ^ Module.finrank ℝ (WithLp 2 (ℝ × V)) *
        convexBodyVolumeReal (toLpConvexBody K) :=
      convexBodyVolumeReal_smul_of_nonneg (toLpConvexBody K) hc
    _ = c ^ Module.finrank ℝ (ℝ × V) *
        (volume (K : Set (ℝ × V))).toReal := by
      rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).toLinearEquiv.finrank_eq,
        convexBodyVolumeReal, volume_toLpConvexBody]

/-- Equal positive real volumes imply the equal-volume
Brunn--Minkowski conclusion in the plain product model. -/
theorem volumeReal_le_weightedMinkowski_of_equal_pos
    (hBM : ∀ (s : ℝ) (A B : ConvexBody V),
      0 ≤ s → s ≤ 1 → BrunnMinkowskiAt s A B)
    (hdim : Module.finrank ℝ V ≠ 0)
    (K L : ConvexBody (ℝ × V)) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hvolEq : (volume (K : Set (ℝ × V))).toReal =
      (volume (L : Set (ℝ × V))).toReal)
    (hvolPos : 0 < (volume (K : Set (ℝ × V))).toReal) :
    (volume (K : Set (ℝ × V))).toReal ≤
      (volume ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) :
        Set (ℝ × V))).toReal := by
  let n : ℕ := Module.finrank ℝ (ℝ × V)
  let m : ℝ := (volume (K : Set (ℝ × V))).toReal
  let c : ℝ := m ^ ((n : ℝ)⁻¹)
  let r : ℝ := c⁻¹
  have hn : n ≠ 0 := by
    dsimp only [n]
    rw [Module.finrank_prod, Module.finrank_self]
    simp
  have hm : 0 < m := hvolPos
  have hc : 0 < c := Real.rpow_pos_of_pos hm _
  have hr : 0 < r := inv_pos.mpr hc
  have hcpow : c ^ n = m := by
    exact Real.rpow_inv_natCast_pow hm.le hn
  have hrpow : r ^ n = m⁻¹ := by
    dsimp only [r]
    rw [inv_pow, hcpow]
  have hKnorm :
      (volume ((r • K : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal = 1 := by
    rw [productConvexBodyVolumeReal_smul_of_nonneg K hr.le]
    change r ^ n * m = 1
    rw [hrpow]
    exact inv_mul_cancel₀ hm.ne'
  have hLnorm :
      (volume ((r • L : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal = 1 := by
    rw [productConvexBodyVolumeReal_smul_of_nonneg L hr.le]
    change r ^ n * (volume (L : Set (ℝ × V))).toReal = 1
    rw [← hvolEq, hrpow]
    exact inv_mul_cancel₀ hm.ne'
  have hnormalized := one_le_volumeReal_weightedMinkowski_of_volumeReal_one
    hBM hdim (r • K) (r • L) ht₀ ht₁ hKnorm hLnorm
  have hbody :
      (1 - t) • (r • K) + t • (r • L) =
        r • ((1 - t) • K + t • L) := by
    calc
      _ = ((1 - t) * r) • K + (t * r) • L := congrArg₂ (fun A B ↦ A + B)
        (smul_smul (1 - t) r K) (smul_smul t r L)
      _ = (r * (1 - t)) • K + (r * t) • L := by
        congr 2 <;> ring
      _ = r • ((1 - t) • K) + r • (t • L) := congrArg₂ (fun A B ↦ A + B)
        (smul_smul r (1 - t) K).symm (smul_smul r t L).symm
      _ = _ := (smul_add r ((1 - t) • K) (t • L)).symm
  rw [hbody, productConvexBodyVolumeReal_smul_of_nonneg _ hr.le] at hnormalized
  change 1 ≤ r ^ n *
    (volume ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) : Set (ℝ × V))).toReal at hnormalized
  rw [hrpow] at hnormalized
  change m ≤ _
  have hnormalized' : 1 ≤
      (volume ((((1 - t) • K + t • L) : ConvexBody (ℝ × V)) :
        Set (ℝ × V))).toReal / m := by
    simpa only [div_eq_mul_inv, mul_comm] using hnormalized
  simpa only [one_mul] using (le_div_iff₀ hm).mp hnormalized'

/-- The full Brunn--Minkowski induction step on the `L²` product.  The
one-dimensional slicing argument is carried out after forgetting the `L²`
norm.  Equal volume roots then give equal ordinary product volumes, and
`brunnMinkowskiAt_of_equal_volume_case` supplies all zero-volume and unequal-
volume cases. -/
theorem brunnMinkowskiAt_withLpProduct_of_lower_dim
    (hBM : ∀ (s : ℝ) (A B : ConvexBody V),
      0 ≤ s → s ≤ 1 → BrunnMinkowskiAt s A B)
    (hdim : Module.finrank ℝ V ≠ 0)
    (K L : ConvexBody (WithLp 2 (ℝ × V))) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    BrunnMinkowskiAt t K L := by
  have hprodDim : Module.finrank ℝ (WithLp 2 (ℝ × V)) ≠ 0 := by
    rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).toLinearEquiv.finrank_eq,
      Module.finrank_prod, Module.finrank_self]
    simp
  apply brunnMinkowskiAt_of_equal_volume_case hprodDim _ K L ht₀ ht₁
  intro s A B hs₀ hs₁ hrootEq
  by_cases hrootZero : convexBodyVolumeRoot A = 0
  · exact brunnMinkowskiAt_of_left_root_eq_zero
      hprodDim A B hs₀ hrootZero
  have hrootPos : 0 < convexBodyVolumeRoot A :=
    lt_of_le_of_ne (convexBodyVolumeRoot_nonneg A) (Ne.symm hrootZero)
  have hcastDim :
      (Module.finrank ℝ (WithLp 2 (ℝ × V)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hprodDim
  have hinvDim :
      ((Module.finrank ℝ (WithLp 2 (ℝ × V)) : ℝ)⁻¹) ≠ 0 :=
    inv_ne_zero hcastDim
  have hvolPos : 0 < convexBodyVolumeReal A := by
    apply lt_of_le_of_ne (convexBodyVolumeReal_nonneg A)
    intro hzero
    apply hrootZero
    rw [convexBodyVolumeRoot, ← hzero, Real.zero_rpow hinvDim]
  have hvolEq : convexBodyVolumeReal A = convexBodyVolumeReal B := by
    apply (Real.rpow_left_inj
      (convexBodyVolumeReal_nonneg A) (convexBodyVolumeReal_nonneg B)
      hinvDim).mp
    simpa only [convexBodyVolumeRoot] using hrootEq
  let A' : ConvexBody (ℝ × V) := ofLpConvexBody A
  let B' : ConvexBody (ℝ × V) := ofLpConvexBody B
  have hrawEq :
      (volume (A' : Set (ℝ × V))).toReal =
        (volume (B' : Set (ℝ × V))).toReal := by
    dsimp only [A', B']
    rw [volume_ofLpConvexBody, volume_ofLpConvexBody]
    exact hvolEq
  have hrawPos : 0 < (volume (A' : Set (ℝ × V))).toReal := by
    dsimp only [A']
    rw [volume_ofLpConvexBody]
    exact hvolPos
  have hrawComparison := volumeReal_le_weightedMinkowski_of_equal_pos
    hBM hdim A' B' hs₀ hs₁ hrawEq hrawPos
  have htransported := brunnMinkowskiAt_toLpConvexBody_of_equal_volume
    s A' B' hrawEq hrawComparison
  simpa only [A', B', toLpConvexBody_ofLpConvexBody] using htransported

end ZeroOrderBounds.AccuracyImprovement
