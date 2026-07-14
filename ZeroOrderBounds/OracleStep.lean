import ZeroOrderBounds.OracleState
import ZeroOrderBounds.QuantileSection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# One resisting-oracle step

At a fixed query, every row body is equipped with its affine row-evaluation
functional and an exact upper quantile.  This file constructs both branches of
the resisting-oracle update and packages all geometric and transcript
invariants needed by the later recursion.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal

namespace ZeroOrderBounds

/-! ## Row affine functionals and the quantile level -/

/-- Continuous affine form of a row's value at a fixed query. -/
def rowFunctional {m : ℕ} (q : QuerySpace m) (i : Fin m) :
    RowSpace m →ᴬ[ℝ] ℝ :=
  (innerSL ℝ (secondBlock q)).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (RowSpace m) (a * firstBlock q i)

@[simp]
theorem rowFunctional_apply {m : ℕ} (q : QuerySpace m) (i : Fin m)
    (w : RowSpace m) :
    rowFunctional q i w = rowEvaluation q i w := by
  simp [rowFunctional, rowEvaluation, real_inner_comm]
  ring

/-- The fixed cap fraction `1 / (4m)`. -/
def oracleAlpha (m : ℕ) : ℝ :=
  1 / (4 * (m : ℝ))

theorem oracleAlpha_pos {m : ℕ} [NeZero m] : 0 < oracleAlpha m := by
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [oracleAlpha]
  positivity

theorem oracleAlpha_lt_one {m : ℕ} [NeZero m] : oracleAlpha m < 1 := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  rw [oracleAlpha]
  have hden : (0 : ℝ) < 4 * (m : ℝ) := by positivity
  apply (div_lt_one₀ hden).2
  nlinarith

/-- Nonconstancy of the row evaluation on its current uncertainty body. -/
def RowNonconstant {m : ℕ} (rows : Fin m → RowBody m)
    (q : QuerySpace m) (i : Fin m) : Prop :=
  NonconstantOn (rowFunctional q i) (rows i : Set (RowSpace m))

/-- A nonconstant functional forces a positive affine dimension. -/
theorem affineDim_ne_zero_of_nonconstantOn {m : ℕ} (P : RowBody m)
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ}
    (hnonconstant : NonconstantOn ℓ (P : Set (RowSpace m))) :
    affineDim (P : Set (RowSpace m)) ≠ 0 := by
  intro hdim
  have hsingleton :=
    eq_singleton_of_nonempty_of_affineDim_eq_zero P.nonempty hdim
  obtain ⟨x, hx, z, hz, hxz⟩ := hnonconstant
  rw [hsingleton] at hx hz
  simp only [mem_singleton_iff] at hx hz
  exact hxz (congrArg ℓ (hx.trans hz.symm))

/-- On a nonempty set, intrinsic volume agrees with Euclidean Hausdorff
measure in the set's affine dimension, including dimension zero. -/
theorem intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Set E} (hP : P.Nonempty) :
    intrinsicVolume P = μHE[affineDim P] P := by
  by_cases hdim : affineDim P = 0
  · rw [intrinsicVolume_of_affineDim_eq_zero hdim, hdim,
      euclideanHausdorffMeasure_zero_of_nonempty_affineDim_zero hP hdim]
  · exact intrinsicVolume_of_affineDim_ne_zero hdim

/-- The exact upper quantile of one row.  On a constant row it is the common
value of the functional. -/
def rowThreshold {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) (i : Fin m) : ℝ := by
  classical
  exact
    if h : RowNonconstant rows q i then
      Classical.choose
        (exists_affineCap_euclideanHausdorffMeasure_eq
          (rows i).nonempty (rows i).isCompact (rows i).convex h
          (oracleAlpha_pos (m := m)) (oracleAlpha_lt_one (m := m)))
    else
      rowFunctional q i (rows i).nonempty.some

theorem rowThreshold_cap_measure {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m) (i : Fin m)
    (hi : RowNonconstant rows q i) :
    μHE[affineDim (rows i : Set (RowSpace m))]
        (affineCap (rows i : Set (RowSpace m)) (rowFunctional q i)
          (rowThreshold rows q i)) =
      ENNReal.ofReal (oracleAlpha m) *
        μHE[affineDim (rows i : Set (RowSpace m))] (rows i : Set (RowSpace m)) := by
  rw [rowThreshold, dif_pos hi]
  exact Classical.choose_spec
    (exists_affineCap_euclideanHausdorffMeasure_eq
      (rows i).nonempty (rows i).isCompact (rows i).convex hi
      (oracleAlpha_pos (m := m)) (oracleAlpha_lt_one (m := m)))

theorem rowThreshold_eq_of_not_nonconstant {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m) (i : Fin m)
    (hi : ¬RowNonconstant rows q i) {w : RowSpace m} (hw : w ∈ rows i) :
    rowFunctional q i w = rowThreshold rows q i := by
  rw [rowThreshold, dif_neg hi]
  by_contra hne
  apply hi
  exact ⟨w, hw, (rows i).nonempty.some,
    (rows i).nonempty.some_mem, hne⟩

/-- Maximum of all row quantiles. -/
def oracleThreshold {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty
    (rowThreshold rows q)

theorem rowThreshold_le_oracleThreshold {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m) (i : Fin m) :
    rowThreshold rows q i ≤ oracleThreshold rows q :=
  Finset.le_sup' (rowThreshold rows q) (Finset.mem_univ i)

theorem exists_rowThreshold_eq_oracleThreshold {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m) :
    ∃ i, rowThreshold rows q i = oracleThreshold rows q := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (rowThreshold rows q)
  exact ⟨i, hi.symm⟩

/-! ## Closed lower cuts -/

/-- The retained lower part of a row body. -/
def affineLowerCut {m : ℕ} (P : Set (RowSpace m))
    (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (y : ℝ) : Set (RowSpace m) :=
  P ∩ ℓ ⁻¹' Iic y

theorem affineLowerCut_subset {m : ℕ} (P : Set (RowSpace m))
    (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (y : ℝ) :
    affineLowerCut P ℓ y ⊆ P :=
  inter_subset_left

theorem isCompact_affineLowerCut {m : ℕ} {P : Set (RowSpace m)}
    (hP : IsCompact P) (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (y : ℝ) :
    IsCompact (affineLowerCut P ℓ y) :=
  hP.inter_right (isClosed_Iic.preimage ℓ.continuous)

theorem convex_affineLowerCut {m : ℕ} {P : Set (RowSpace m)}
    (hP : Convex ℝ P) (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (y : ℝ) :
    Convex ℝ (affineLowerCut P ℓ y) :=
  hP.inter ((convex_Iic y).affine_preimage ℓ.toAffineMap)

/-- The complement-of-cap estimate underlying every unselected update. -/
theorem affineLowerCut_measure_lower {m : ℕ} (P : RowBody m)
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ}
    (_hnonconstant : NonconstantOn ℓ (P : Set (RowSpace m)))
    {α r y : ℝ} (hα0 : 0 < α) (_hα1 : α < 1) (hry : r ≤ y)
    (hquantile :
      μHE[affineDim (P : Set (RowSpace m))]
          (affineCap (P : Set (RowSpace m)) ℓ r) =
        ENNReal.ofReal α *
          μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m))) :
    ENNReal.ofReal (1 - α) *
        μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m)) ≤
      μHE[affineDim (P : Set (RowSpace m))]
        (affineLowerCut (P : Set (RowSpace m)) ℓ y) := by
  let μ : Measure (RowSpace m) := μHE[affineDim (P : Set (RowSpace m))]
  let L := affineLowerCut (P : Set (RowSpace m)) ℓ y
  let C := affineCap (P : Set (RowSpace m)) ℓ r
  have hcover : (P : Set (RowSpace m)) ⊆ L ∪ C := by
    intro w hw
    by_cases hwy : ℓ w ≤ y
    · exact Or.inl ⟨hw, hwy⟩
    · exact Or.inr ⟨hw, hry.trans (le_of_not_ge hwy)⟩
  have hmeasure : μ (P : Set (RowSpace m)) ≤ μ L + μ C :=
    (measure_mono hcover).trans (measure_union_le L C)
  have hPfinite : μ (P : Set (RowSpace m)) < ⊤ :=
    euclideanHausdorffMeasure_affineDim_lt_top P.nonempty P.isCompact
  have hCfinite : μ C < ⊤ :=
    (measure_mono (affineCap_subset (P : Set (RowSpace m)) ℓ r)).trans_lt hPfinite
  have hsub : μ (P : Set (RowSpace m)) - μ C ≤ μ L := by
    calc
      μ (P : Set (RowSpace m)) - μ C ≤ (μ L + μ C) - μ C :=
        tsub_le_tsub_right hmeasure (μ C)
      _ = μ L := ENNReal.add_sub_cancel_right hCfinite.ne
  have hfactor :
      ENNReal.ofReal (1 - α) * μ (P : Set (RowSpace m)) =
        μ (P : Set (RowSpace m)) - ENNReal.ofReal α * μ (P : Set (RowSpace m)) := by
    rw [ENNReal.ofReal_sub 1 hα0.le, ENNReal.ofReal_one]
    calc
      (1 - ENNReal.ofReal α) * μ (P : Set (RowSpace m)) =
          1 * μ (P : Set (RowSpace m)) -
            ENNReal.ofReal α * μ (P : Set (RowSpace m)) :=
        ENNReal.sub_mul (fun _ _ ↦ hPfinite.ne)
      _ = μ (P : Set (RowSpace m)) -
          ENNReal.ofReal α * μ (P : Set (RowSpace m)) := by rw [one_mul]
  change ENNReal.ofReal (1 - α) * μ (P : Set (RowSpace m)) ≤ μ L
  rw [hfactor, ← hquantile]
  exact hsub

/-- Data supplied by retaining a nonconstant row below a level at or above its
upper quantile. -/
structure LowerCutResult {m : ℕ} (P : RowBody m)
    (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (y α : ℝ) where
  body : RowBody m
  carrier_eq : (body : Set (RowSpace m)) = affineLowerCut (P : Set (RowSpace m)) ℓ y
  subset_old : (body : Set (RowSpace m)) ⊆ P
  dim_eq : body.dim = P.dim
  volume_lower : ENNReal.ofReal (1 - α) * P.volume ≤ body.volume

/-- Construct the retained lower body and all of its quantitative invariants. -/
theorem exists_lowerCutResult {m : ℕ} (P : RowBody m)
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ}
    (hnonconstant : NonconstantOn ℓ (P : Set (RowSpace m)))
    {α r y : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hry : r ≤ y)
    (hquantile :
      μHE[affineDim (P : Set (RowSpace m))]
          (affineCap (P : Set (RowSpace m)) ℓ r) =
        ENNReal.ofReal α *
          μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m))) :
    Nonempty (LowerCutResult P ℓ y α) := by
  let Q := affineLowerCut (P : Set (RowSpace m)) ℓ y
  have hmeasure := affineLowerCut_measure_lower P hnonconstant hα0 hα1 hry hquantile
  have hPmeasurepos :
      0 < μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m)) := by
    rw [← intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty P.nonempty]
    exact P.volume_pos
  have hfactorpos : 0 < ENNReal.ofReal (1 - α) *
      μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m)) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr hα1)).ne'
      hPmeasurepos.ne'
  have hQmeasurepos : 0 < μHE[affineDim (P : Set (RowSpace m))] Q :=
    hfactorpos.trans_le hmeasure
  have hQne : Q.Nonempty := nonempty_of_euclideanHausdorffMeasure_pos hQmeasurepos
  have hQcompact : IsCompact Q := isCompact_affineLowerCut P.isCompact ℓ y
  have hQconvex : Convex ℝ Q := convex_affineLowerCut P.convex ℓ y
  have hQball : Q ⊆ closedBall (0 : RowSpace m) (tau m) :=
    (affineLowerCut_subset (P : Set (RowSpace m)) ℓ y).trans P.subset_initial
  let B := RowBody.ofCompactConvex Q hQne hQcompact hQconvex hQball
  have hdim : affineDim Q = affineDim (P : Set (RowSpace m)) :=
    affineDim_eq_of_positive_measure_subset hQcompact
      (affineLowerCut_subset (P : Set (RowSpace m)) ℓ y) hQmeasurepos
  refine ⟨{
    body := B
    carrier_eq := rfl
    subset_old := affineLowerCut_subset (P : Set (RowSpace m)) ℓ y
    dim_eq := ?_
    volume_lower := ?_ }⟩
  · exact hdim
  · change ENNReal.ofReal (1 - α) * intrinsicVolume (P : Set (RowSpace m)) ≤
      intrinsicVolume Q
    rw [intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty P.nonempty,
      intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty hQne, hdim]
    exact hmeasure

/-! ## Large selected sections -/

/-- Data supplied by the codimension-one selected-row update. -/
structure SectionResult {m : ℕ} (P : RowBody m)
    (ℓ : RowSpace m →ᴬ[ℝ] ℝ) (r : ℝ) where
  level : ℝ
  threshold_le : r ≤ level
  body : RowBody m
  carrier_eq : (body : Set (RowSpace m)) = affineSection (P : Set (RowSpace m)) ℓ level
  subset_old : (body : Set (RowSpace m)) ⊆ P
  dim_eq : body.dim = P.dim - 1
  volume_lower :
    P.volume / ENNReal.ofReal (8 * (m : ℝ) * tau m) ≤ body.volume

/-- The numerical cap-to-section factor is exactly `1 / (8mτ)`. -/
theorem oracle_section_scale {m : ℕ} [NeZero m] (V : ENNReal) (hV : V < ⊤) :
    ENNReal.ofReal (oracleAlpha m) * V / ENNReal.ofReal (2 * tau m) =
      V / ENNReal.ofReal (8 * (m : ℝ) * tau m) := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have ht : 0 < tau m := tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))
  have hleft : ENNReal.ofReal (oracleAlpha m) * V / ENNReal.ofReal (2 * tau m) < ⊤ :=
    ENNReal.div_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV).ne
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hright : V / ENNReal.ofReal (8 * (m : ℝ) * tau m) < ⊤ :=
    ENNReal.div_lt_top hV.ne (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  apply (ENNReal.toReal_eq_toReal_iff' hleft.ne hright.ne).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_div]
  simp only [ENNReal.toReal_ofReal (oracleAlpha_pos (m := m)).le,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * tau m by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ 8 * (m : ℝ) * tau m by positivity)]
  rw [oracleAlpha]
  field_simp
  ring

/-- Select a large section above an exact oracle quantile. -/
theorem exists_sectionResult {m : ℕ} [NeZero m] (P : RowBody m)
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ}
    (hnonconstant : NonconstantOn ℓ (P : Set (RowSpace m))) {r : ℝ}
    (hquantile :
      μHE[affineDim (P : Set (RowSpace m))]
          (affineCap (P : Set (RowSpace m)) ℓ r) =
        ENNReal.ofReal (oracleAlpha m) *
          μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m))) :
    Nonempty (SectionResult P ℓ r) := by
  have ht : 0 < tau m := tau_pos (Nat.pos_of_ne_zero (NeZero.ne m))
  have hPmeasurepos :
      0 < μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m)) := by
    rw [← intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty P.nonempty]
    exact P.volume_pos
  have hcap_pos : 0 < μHE[affineDim (P : Set (RowSpace m))]
      (affineCap (P : Set (RowSpace m)) ℓ r) := by
    rw [hquantile]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (oracleAlpha_pos (m := m))).ne'
      hPmeasurepos.ne'
  obtain ⟨y, hry, hlarge, hQne, hQcompact, hQconvex, hdim⟩ :=
    exists_large_affineSection P.nonempty P.isCompact P.convex hnonconstant
      ht P.subset_initial hcap_pos
  let Q := affineSection (P : Set (RowSpace m)) ℓ y
  have hQball : Q ⊆ closedBall (0 : RowSpace m) (tau m) :=
    (affineSection_subset (P : Set (RowSpace m)) ℓ y).trans P.subset_initial
  let B := RowBody.ofCompactConvex Q hQne hQcompact hQconvex hQball
  refine ⟨{
    level := y
    threshold_le := hry
    body := B
    carrier_eq := rfl
    subset_old := affineSection_subset (P : Set (RowSpace m)) ℓ y
    dim_eq := hdim
    volume_lower := ?_ }⟩
  change intrinsicVolume (P : Set (RowSpace m)) /
      ENNReal.ofReal (8 * (m : ℝ) * tau m) ≤ intrinsicVolume Q
  rw [intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty P.nonempty,
    intrinsicVolume_eq_euclideanHausdorffMeasure_affineDim_of_nonempty hQne,
    hdim]
  rw [← oracle_section_scale
    (μHE[affineDim (P : Set (RowSpace m))] (P : Set (RowSpace m)))
      (euclideanHausdorffMeasure_affineDim_lt_top P.nonempty P.isCompact),
    ← hquantile]
  exact hlarge

/-! ## Real-volume forms used by the recursive potential -/

theorem LowerCutResult.volumeReal_lower {m : ℕ} {P : RowBody m}
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ} {y α : ℝ} (R : LowerCutResult P ℓ y α)
    (hα : α ≤ 1) :
    (1 - α) * P.volumeReal ≤ R.body.volumeReal := by
  have h := ENNReal.toReal_mono R.body.volume_lt_top.ne R.volume_lower
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hα)] at h
  exact h

theorem SectionResult.volumeReal_lower {m : ℕ} [NeZero m]
    {P : RowBody m} {ℓ : RowSpace m →ᴬ[ℝ] ℝ} {r : ℝ}
    (R : SectionResult P ℓ r) :
    P.volumeReal / (8 * (m : ℝ) * tau m) ≤ R.body.volumeReal := by
  have h := ENNReal.toReal_mono R.body.volume_lt_top.ne R.volume_lower
  rw [ENNReal.toReal_div,
    ENNReal.toReal_ofReal (show 0 ≤ 8 * (m : ℝ) * tau m by
      have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have ht : 0 < tau m := tau_pos hm
      positivity)] at h
  exact h

theorem LowerCutResult.mem_iff {m : ℕ} {P : RowBody m}
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ} {y α : ℝ} (R : LowerCutResult P ℓ y α)
    {w : RowSpace m} :
    w ∈ R.body ↔ w ∈ P ∧ ℓ w ≤ y := by
  change w ∈ (R.body : Set (RowSpace m)) ↔ _
  rw [R.carrier_eq]
  rfl

theorem SectionResult.mem_iff {m : ℕ} {P : RowBody m}
    {ℓ : RowSpace m →ᴬ[ℝ] ℝ} {r : ℝ} (R : SectionResult P ℓ r)
    {w : RowSpace m} :
    w ∈ R.body ↔ w ∈ P ∧ ℓ w = R.level := by
  change w ∈ (R.body : Set (RowSpace m)) ↔ _
  rw [R.carrier_eq]
  rfl

/-! ## The bundled transition interface -/

/-- An informative round is one where a nonconstant row attains the maximum
row threshold. -/
def Informative {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) : Prop :=
  ∃ i, RowNonconstant rows q i ∧
    rowThreshold rows q i = oracleThreshold rows q

/-- Least informative row, matching the deterministic tie-breaking convention. -/
def informativeIndex {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) (h : Informative rows q) : Fin m := by
  classical
  let candidates := (Finset.univ : Finset (Fin m)).filter fun i ↦
    RowNonconstant rows q i ∧ rowThreshold rows q i = oracleThreshold rows q
  have hcandidates : candidates.Nonempty := by
    obtain ⟨i, hi, hr⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hr⟩⟩
  exact candidates.min' hcandidates

theorem informativeIndex_spec {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m)
    (h : Informative rows q) :
    RowNonconstant rows q (informativeIndex rows q h) ∧
      rowThreshold rows q (informativeIndex rows q h) = oracleThreshold rows q := by
  classical
  let candidates := (Finset.univ : Finset (Fin m)).filter fun i ↦
    RowNonconstant rows q i ∧ rowThreshold rows q i = oracleThreshold rows q
  have hcandidates : candidates.Nonempty := by
    obtain ⟨i, hi, hr⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hr⟩⟩
  have hmem := Finset.min'_mem candidates hcandidates
  simpa only [informativeIndex, candidates, Finset.mem_filter,
    Finset.mem_univ, true_and] using hmem

theorem informativeIndex_le {m : ℕ} [NeZero m]
    (rows : Fin m → RowBody m) (q : QuerySpace m)
    (h : Informative rows q) (j : Fin m)
    (hj : RowNonconstant rows q j)
    (hjr : rowThreshold rows q j = oracleThreshold rows q) :
    informativeIndex rows q h ≤ j := by
  classical
  let candidates := (Finset.univ : Finset (Fin m)).filter fun i ↦
    RowNonconstant rows q i ∧ rowThreshold rows q i = oracleThreshold rows q
  have hcandidates : candidates.Nonempty := by
    obtain ⟨i, hi, hr⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hr⟩⟩
  have hjmem : j ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hjr⟩
  simpa only [informativeIndex, candidates] using
    Finset.min'_le candidates j hjmem

/-- Complete output of one oracle transition.  The fields are deliberately
oriented toward iteration and product-volume bookkeeping. -/
structure StepResult {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) where
  answer : ℝ
  rows : Fin m → RowBody m
  selected : Option (Fin m)
  subset_old : ∀ i, (rows i : Set (RowSpace m)) ⊆ S.rows i
  rows_answer : RowsAnswerAt rows (S.nextQuery : QuerySpace m) answer
  selected_nonconstant : ∀ {i}, selected = some i →
    RowNonconstant S.rows (S.nextQuery : QuerySpace m) i
  selected_dim : ∀ {i}, selected = some i →
    (rows i).dim = (S.rows i).dim - 1
  selected_volumeReal : ∀ {i}, selected = some i →
    (S.rows i).volumeReal / (8 * (m : ℝ) * tau m) ≤ (rows i).volumeReal
  unselected_dim : ∀ i, selected ≠ some i →
    (rows i).dim = (S.rows i).dim
  unselected_volumeReal : ∀ i, selected ≠ some i →
    RowNonconstant S.rows (S.nextQuery : QuerySpace m) i →
    (1 - oracleAlpha m) * (S.rows i).volumeReal ≤ (rows i).volumeReal
  constant_unchanged : ∀ i,
    ¬RowNonconstant S.rows (S.nextQuery : QuerySpace m) i → rows i = S.rows i

namespace StepResult

variable {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
  {S : OracleState A}

/-- The successor state, with exact transcript consistency supplied by
`rows_answer`. -/
def state (R : StepResult S) : OracleState A :=
  S.extendOfRowsAnswerAt R.rows R.answer R.subset_old R.rows_answer

@[simp]
theorem state_answers (R : StepResult S) :
    R.state.answers = S.answers ++ [R.answer] :=
  rfl

@[simp]
theorem state_rows (R : StepResult S) : R.state.rows = R.rows :=
  rfl

@[simp]
theorem state_round (R : StepResult S) : R.state.round = S.round + 1 := by
  simp only [OracleState.round, state_answers, List.length_append,
    List.length_singleton]

theorem state_product_consistent (R : StepResult S) :
    ProductConsistent A R.state.answers R.state.rows :=
  R.state.product_consistent

/-- Every unselected row has the retention bound.  For constant rows this is
deduced from exact equality of bodies. -/
theorem retained_volumeReal (R : StepResult S) (i : Fin m)
    (hi : R.selected ≠ some i) :
    (1 - oracleAlpha m) * (S.rows i).volumeReal ≤ (R.rows i).volumeReal := by
  by_cases hnon : RowNonconstant S.rows (S.nextQuery : QuerySpace m) i
  · exact R.unselected_volumeReal i hi hnon
  · rw [R.constant_unchanged i hnon]
    have hα : 0 ≤ oracleAlpha m := (oracleAlpha_pos (m := m)).le
    have hV : 0 ≤ (S.rows i).volumeReal := (S.rows i).volumeReal_pos.le
    nlinarith

theorem dim_eq_of_selected_eq_none (R : StepResult S)
    (hsel : R.selected = none) (i : Fin m) :
    (R.rows i).dim = (S.rows i).dim := by
  apply R.unselected_dim i
  rw [hsel]
  simp

theorem volumeReal_lower_of_selected_eq_none (R : StepResult S)
    (hsel : R.selected = none) (i : Fin m) :
    (1 - oracleAlpha m) * (S.rows i).volumeReal ≤ (R.rows i).volumeReal := by
  apply R.retained_volumeReal i
  rw [hsel]
  simp

theorem dim_eq_of_selected_eq_some_of_ne (R : StepResult S) {j : Fin m}
    (hsel : R.selected = some j) {i : Fin m} (hij : i ≠ j) :
    (R.rows i).dim = (S.rows i).dim := by
  apply R.unselected_dim i
  rw [hsel]
  intro h
  exact hij (Option.some.inj h).symm

theorem volumeReal_lower_of_selected_eq_some_of_ne (R : StepResult S)
    {j : Fin m} (hsel : R.selected = some j) {i : Fin m} (hij : i ≠ j) :
    (1 - oracleAlpha m) * (S.rows i).volumeReal ≤ (R.rows i).volumeReal := by
  apply R.retained_volumeReal i
  rw [hsel]
  intro h
  exact hij (Option.some.inj h).symm

end StepResult

/-! ## Canonical geometric choices for each branch -/

/-- Chosen lower-cut certificate for one nonconstant row. -/
def chosenLowerCut {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) (i : Fin m) (y : ℝ)
    (hi : RowNonconstant rows q i)
    (hiy : rowThreshold rows q i ≤ y) :
    LowerCutResult (rows i) (rowFunctional q i) y (oracleAlpha m) :=
  Classical.choice
    (exists_lowerCutResult (rows i) hi
      (oracleAlpha_pos (m := m)) (oracleAlpha_lt_one (m := m)) hiy
      (rowThreshold_cap_measure rows q i hi))

/-- Chosen large-section certificate for a nonconstant row at its exact
quantile. -/
def chosenSection {m : ℕ} [NeZero m] (rows : Fin m → RowBody m)
    (q : QuerySpace m) (i : Fin m) (hi : RowNonconstant rows q i) :
    SectionResult (rows i) (rowFunctional q i) (rowThreshold rows q i) :=
  Classical.choice
    (exists_sectionResult (rows i) hi (rowThreshold_cap_measure rows q i hi))

/-! ## Informative branch -/

/-- Existence of the informative transition, using the least nonconstant row
attaining the maximum threshold. -/
theorem exists_informativeStepResult {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A)
    (hinfo : Informative S.rows (S.nextQuery : QuerySpace m)) :
    Nonempty (StepResult S) := by
  classical
  let q : QuerySpace m := S.nextQuery
  let i : Fin m := informativeIndex S.rows q hinfo
  have hi : RowNonconstant S.rows q i ∧
      rowThreshold S.rows q i = oracleThreshold S.rows q :=
    informativeIndex_spec S.rows q hinfo
  let R : SectionResult (S.rows i) (rowFunctional q i)
      (rowThreshold S.rows q i) := chosenSection S.rows q i hi.1
  let y : ℝ := R.level
  have hglobal_y : oracleThreshold S.rows q ≤ y := by
    rw [← hi.2]
    exact R.threshold_le
  have hrow_y (j : Fin m) : rowThreshold S.rows q j ≤ y :=
    (rowThreshold_le_oracleThreshold S.rows q j).trans hglobal_y
  let C (j : Fin m) (hj : RowNonconstant S.rows q j) :
      LowerCutResult (S.rows j) (rowFunctional q j) y (oracleAlpha m) :=
    chosenLowerCut S.rows q j y hj (hrow_y j)
  let newRows : Fin m → RowBody m := fun j ↦
    if hji : j = i then R.body
    else if hj : RowNonconstant S.rows q j then (C j hj).body
    else S.rows j
  have hsub : ∀ j, (newRows j : Set (RowSpace m)) ⊆ S.rows j := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [newRows, dif_pos rfl] using R.subset_old
    · simp only [newRows, dif_neg hji]
      by_cases hj : RowNonconstant S.rows q j
      · simpa only [dif_pos hj] using (C j hj).subset_old
      · simp only [dif_neg hj]
        exact subset_rfl
  have hanswer : RowsAnswerAt newRows q y := by
    constructor
    · intro j w hw
      by_cases hji : j = i
      · subst j
        have hwR : w ∈ R.body := by
          simpa only [newRows, dif_pos rfl] using hw
        have hlevel := (SectionResult.mem_iff R).mp hwR |>.2
        simpa only [← rowFunctional_apply] using hlevel.le
      · simp only [newRows, dif_neg hji] at hw
        by_cases hj : RowNonconstant S.rows q j
        · have hwC : w ∈ (C j hj).body := by simpa only [dif_pos hj] using hw
          have hle := (LowerCutResult.mem_iff (C j hj)).mp hwC |>.2
          simpa only [← rowFunctional_apply] using hle
        · have hwold : w ∈ S.rows j := by simpa only [dif_neg hj] using hw
          have heq := rowThreshold_eq_of_not_nonconstant S.rows q j hj hwold
          have hle := (rowThreshold_le_oracleThreshold S.rows q j).trans hglobal_y
          simpa only [← rowFunctional_apply] using heq.le.trans hle
    · refine ⟨i, ?_⟩
      intro w hw
      have hwR : w ∈ R.body := by
        simpa only [newRows, dif_pos rfl] using hw
      have hlevel := (SectionResult.mem_iff R).mp hwR |>.2
      simpa only [← rowFunctional_apply] using hlevel
  refine ⟨{
    answer := y
    rows := newRows
    selected := some i
    subset_old := hsub
    rows_answer := hanswer
    selected_nonconstant := ?_
    selected_dim := ?_
    selected_volumeReal := ?_
    unselected_dim := ?_
    unselected_volumeReal := ?_
    constant_unchanged := ?_ }⟩
  · intro j hj
    have hji : j = i := Option.some.inj hj.symm
    subst j
    exact hi.1
  · intro j hj
    have hji : j = i := Option.some.inj hj.symm
    subst j
    simpa only [newRows, dif_pos rfl] using R.dim_eq
  · intro j hj
    have hji : j = i := Option.some.inj hj.symm
    subst j
    simpa only [newRows, dif_pos rfl] using R.volumeReal_lower
  · intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hj rfl
    simp only [newRows, dif_neg hji]
    by_cases hjnon : RowNonconstant S.rows q j
    · simpa only [dif_pos hjnon] using (C j hjnon).dim_eq
    · simp only [dif_neg hjnon]
  · intro j hj hjnon
    have hji : j ≠ i := by
      intro h
      subst j
      exact hj rfl
    simpa only [newRows, q, dif_neg hji, dif_pos hjnon] using
      (C j hjnon).volumeReal_lower (oracleAlpha_lt_one (m := m)).le
  · intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hj hi.1
    simp only [newRows, q, dif_neg hji, dif_neg hj]

/-! ## Noninformative branch -/

/-- Existence of the noninformative transition.  Every nonconstant row is
lower-cut at the common maximum, while every constant row is unchanged. -/
theorem exists_noninformativeStepResult {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A)
    (hinfo : ¬Informative S.rows (S.nextQuery : QuerySpace m)) :
    Nonempty (StepResult S) := by
  classical
  let q : QuerySpace m := S.nextQuery
  let y : ℝ := oracleThreshold S.rows q
  obtain ⟨i, hi⟩ := exists_rowThreshold_eq_oracleThreshold S.rows q
  have hi_const : ¬RowNonconstant S.rows q i := by
    intro hinon
    exact hinfo ⟨i, hinon, hi⟩
  have hrow_y (j : Fin m) : rowThreshold S.rows q j ≤ y :=
    rowThreshold_le_oracleThreshold S.rows q j
  let C (j : Fin m) (hj : RowNonconstant S.rows q j) :
      LowerCutResult (S.rows j) (rowFunctional q j) y (oracleAlpha m) :=
    chosenLowerCut S.rows q j y hj (hrow_y j)
  let newRows : Fin m → RowBody m := fun j ↦
    if hj : RowNonconstant S.rows q j then (C j hj).body else S.rows j
  have hsub : ∀ j, (newRows j : Set (RowSpace m)) ⊆ S.rows j := by
    intro j
    simp only [newRows]
    by_cases hj : RowNonconstant S.rows q j
    · simpa only [dif_pos hj] using (C j hj).subset_old
    · simp only [dif_neg hj]
      exact subset_rfl
  have hanswer : RowsAnswerAt newRows q y := by
    constructor
    · intro j w hw
      simp only [newRows] at hw
      by_cases hj : RowNonconstant S.rows q j
      · have hwC : w ∈ (C j hj).body := by simpa only [dif_pos hj] using hw
        have hle := (LowerCutResult.mem_iff (C j hj)).mp hwC |>.2
        simpa only [← rowFunctional_apply] using hle
      · have hwold : w ∈ S.rows j := by simpa only [dif_neg hj] using hw
        have heq := rowThreshold_eq_of_not_nonconstant S.rows q j hj hwold
        have hle := rowThreshold_le_oracleThreshold S.rows q j
        simpa only [← rowFunctional_apply] using heq.le.trans hle
    · refine ⟨i, ?_⟩
      intro w hw
      have hwold : w ∈ S.rows i := by
        simpa only [newRows, dif_neg hi_const] using hw
      have heq := rowThreshold_eq_of_not_nonconstant S.rows q i hi_const hwold
      rw [hi] at heq
      simpa only [← rowFunctional_apply] using heq
  refine ⟨{
    answer := y
    rows := newRows
    selected := none
    subset_old := hsub
    rows_answer := hanswer
    selected_nonconstant := ?_
    selected_dim := ?_
    selected_volumeReal := ?_
    unselected_dim := ?_
    unselected_volumeReal := ?_
    constant_unchanged := ?_ }⟩
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj
  · intro j _
    simp only [newRows]
    by_cases hj : RowNonconstant S.rows q j
    · simpa only [dif_pos hj] using (C j hj).dim_eq
    · simp only [dif_neg hj]
  · intro j _ hj
    simpa only [newRows, q, dif_pos hj] using
      (C j hj).volumeReal_lower (oracleAlpha_lt_one (m := m)).le
  · intro j hj
    simp only [newRows, q, dif_neg hj]

/-! ## Total chosen transition -/

theorem stepResult_nonempty {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A) :
    Nonempty (StepResult S) := by
  by_cases hinfo : Informative S.rows (S.nextQuery : QuerySpace m)
  · exact exists_informativeStepResult S hinfo
  · exact exists_noninformativeStepResult S hinfo

/-- The total noncomputable resisting-oracle transition certificate. -/
def oracleStep {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) : StepResult S :=
  Classical.choice (stepResult_nonempty S)

/-- The successor state alone, for convenient iteration. -/
def oracleNextState {m : ℕ} [NeZero m] {A : DeterministicStrategy m}
    (S : OracleState A) : OracleState A :=
  (oracleStep S).state

@[simp]
theorem oracleNextState_round {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A) :
    (oracleNextState S).round = S.round + 1 :=
  (oracleStep S).state_round

@[simp]
theorem oracleNextState_rows {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A) :
    (oracleNextState S).rows = (oracleStep S).rows :=
  rfl

@[simp]
theorem oracleNextState_answers {m : ℕ} [NeZero m]
    {A : DeterministicStrategy m} (S : OracleState A) :
    (oracleNextState S).answers = S.answers ++ [(oracleStep S).answer] :=
  rfl

end ZeroOrderBounds
