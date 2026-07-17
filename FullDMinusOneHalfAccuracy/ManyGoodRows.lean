import ZeroOrderBounds.OracleRun
import FullDMinusOneHalfAccuracy.Numerics
import Mathlib.Tactic

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Many rows retain high dimension and normalized volume radius

The existing oracle potential gives a total codimension budget and a total
entropy budget.  At the paper horizon, two elementary superlevel estimates
show that at least half of all rows simultaneously retain `24/25` of their
dimension and have entropy at most `4m/25`.  Their entropy per surviving
dimension is therefore at most `1/6`.
-/

noncomputable section

open scoped BigOperators

namespace ZeroOrderBounds.AccuracyImprovement

/-- The two numerical conditions defining a good row. -/
def IsGoodRow {m : ℕ} (c : Fin m → ℕ) (rho : Fin m → ℝ)
    (i : Fin m) : Prop :=
  25 * (c i : ℝ) ≤ (m : ℝ) ∧
    25 * rowEntropy (rho i) ≤ 4 * (m : ℝ)

instance {m : ℕ} (c : Fin m → ℕ) (rho : Fin m → ℝ) :
    DecidablePred (IsGoodRow c rho) :=
  Classical.decPred _

/-- The canonical finset of rows satisfying both good-row inequalities. -/
def goodRows {m : ℕ} (c : Fin m → ℕ) (rho : Fin m → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter (IsGoodRow c rho)

@[simp]
theorem mem_goodRows {m : ℕ} {c : Fin m → ℕ} {rho : Fin m → ℝ}
    {i : Fin m} :
    i ∈ goodRows c rho ↔ IsGoodRow c rho i := by
  simp [goodRows]

/-- Finite Markov inequality in the exact form used below: the size of a
strict superlevel set times its threshold is bounded by the total sum. -/
theorem card_strictSuperlevel_mul_le_sum
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (q : ℝ) (hf : ∀ i, 0 ≤ f i) :
    (((Finset.univ.filter fun i ↦ q < f i).card : ℕ) : ℝ) * q ≤
      ∑ i, f i := by
  let s : Finset ι := Finset.univ.filter fun i ↦ q < f i
  calc
    (s.card : ℝ) * q = ∑ _i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, f i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ ↦ hf i)

/-- Under the paper horizon, at most a quarter of the rows have codimension
larger than `m/25`. -/
theorem four_mul_card_bad_codimension_le {m T : ℕ} (hm : 0 < m)
    (c : Fin m → ℕ) (hcRounds : ∑ i, c i ≤ T)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    4 * (Finset.univ.filter
      (fun i ↦ (m : ℝ) < 25 * (c i : ℝ))).card ≤ m := by
  let B : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ (m : ℝ) < 25 * (c i : ℝ))
  have hmarkov := card_strictSuperlevel_mul_le_sum
    (fun i ↦ 25 * (c i : ℝ)) (m : ℝ) (fun _ ↦ by positivity)
  change (B.card : ℝ) * (m : ℝ) ≤
    ∑ i : Fin m, 25 * (c i : ℝ) at hmarkov
  have hsumCast : ∑ i, (c i : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hcRounds
  have hsum : (B.card : ℝ) * (m : ℝ) ≤ 25 * (T : ℝ) := by
    rw [← Finset.mul_sum] at hmarkov
    exact hmarkov.trans (mul_le_mul_of_nonneg_left hsumCast (by norm_num))
  have hbudget := hundred_mul_horizon_le_square hm horizon
  by_contra hcard
  have hcardNat : m < 4 * B.card := Nat.lt_of_not_ge hcard
  have hcardR : (m : ℝ) < 4 * (B.card : ℝ) := by exact_mod_cast hcardNat
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmul := mul_lt_mul_of_pos_right hcardR hmR
  nlinarith

/-- Under the paper horizon, at most a quarter of the rows have entropy
larger than `4m/25`. -/
theorem four_mul_card_bad_entropy_le {m T : ℕ} (hm : 0 < m)
    (rho : Fin m → ℝ)
    (hrho_pos : ∀ i, 0 < rho i) (hrho_one : ∀ i, rho i ≤ 1)
    (hEntropyRounds :
      ∑ i, rowEntropy (rho i) ≤ (T : ℝ) * entropyScale m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    4 * (Finset.univ.filter
      (fun i ↦ 4 * (m : ℝ) < 25 * rowEntropy (rho i))).card ≤ m := by
  let B : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ 4 * (m : ℝ) < 25 * rowEntropy (rho i))
  have hDnonneg : ∀ i, 0 ≤ rowEntropy (rho i) :=
    fun i ↦ rowEntropy_nonneg (hrho_pos i) (hrho_one i)
  have hmarkov := card_strictSuperlevel_mul_le_sum
    (fun i ↦ 25 * rowEntropy (rho i)) (4 * (m : ℝ))
    (fun i ↦ mul_nonneg (by norm_num) (hDnonneg i))
  change (B.card : ℝ) * (4 * (m : ℝ)) ≤
    ∑ i : Fin m, 25 * rowEntropy (rho i) at hmarkov
  have hsum : (B.card : ℝ) * (4 * (m : ℝ)) ≤
      25 * ((T : ℝ) * entropyScale m) := by
    rw [← Finset.mul_sum] at hmarkov
    exact hmarkov.trans
      (mul_le_mul_of_nonneg_left hEntropyRounds (by norm_num))
  have hbudget := twentyfive_mul_horizon_entropyScale_le_square hm horizon
  by_contra hcard
  have hcardNat : m < 4 * B.card := Nat.lt_of_not_ge hcard
  have hcardR : (m : ℝ) < 4 * (B.card : ℝ) := by exact_mod_cast hcardNat
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmul := mul_lt_mul_of_pos_right hcardR hmR
  nlinarith

/-- A good codimension leaves at least `24/25` of the original dimension. -/
theorem dimension_high_of_good_codimension {m c k : ℕ}
    (hm : 0 < m) (hk : k = m - c)
    (hc : 25 * (c : ℝ) ≤ (m : ℝ)) :
    24 * m ≤ 25 * k ∧ 0 < k := by
  have hcNat : 25 * c ≤ m := by exact_mod_cast hc
  subst k
  constructor <;> omega

/-- The normalized volume radius of a good row is at least `exp (-1/6)`. -/
theorem normalizedVolumeRadius_ge_exp_neg_one_sixth
    {m c k : ℕ} {rho : ℝ}
    (hm : 0 < m) (hk : k = m - c)
    (hrho : 0 < rho)
    (hc : 25 * (c : ℝ) ≤ (m : ℝ))
    (hD : 25 * rowEntropy rho ≤ 4 * (m : ℝ)) :
    Real.exp (-(1 : ℝ) / 6) ≤ rho ^ ((k : ℝ)⁻¹) := by
  obtain ⟨hdim, hkpos⟩ := dimension_high_of_good_codimension hm hk hc
  have hdimR : 24 * (m : ℝ) ≤ 25 * (k : ℝ) := by exact_mod_cast hdim
  have hDk : 6 * rowEntropy rho ≤ (k : ℝ) := by
    nlinarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hlogrho : Real.log rho = -rowEntropy rho := by
    rw [rowEntropy]
    ring
  rw [Real.rpow_def_of_pos hrho, hlogrho]
  apply Real.exp_le_exp.mpr
  rw [show -rowEntropy rho * (k : ℝ)⁻¹ =
    -rowEntropy rho / (k : ℝ) by rw [div_eq_mul_inv]]
  rw [le_div_iff₀ hkR]
  nlinarith

/-- Abstract many-good-rows theorem in the round-budget form returned by the
existing oracle run. -/
theorem many_good_rows_of_round_budgets {m T : ℕ} (hm : 0 < m)
    (c k : Fin m → ℕ) (rho : Fin m → ℝ)
    (hk : ∀ i, k i = m - c i)
    (hrho_pos : ∀ i, 0 < rho i) (hrho_one : ∀ i, rho i ≤ 1)
    (hcRounds : ∑ i, c i ≤ T)
    (hEntropyRounds :
      ∑ i, rowEntropy (rho i) ≤ (T : ℝ) * entropyScale m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    ∃ G : Finset (Fin m),
      m / 2 ≤ G.card ∧ m ≤ 2 * G.card ∧
      ∀ i ∈ G,
        25 * (c i : ℝ) ≤ (m : ℝ) ∧
        24 * m ≤ 25 * k i ∧
        0 < k i ∧
        Real.exp (-(1 : ℝ) / 6) ≤ rho i ^ (((k i : ℕ) : ℝ)⁻¹) ∧
        (1 / 2 : ℝ) < rho i ^ (((k i : ℕ) : ℝ)⁻¹) := by
  let BC : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ (m : ℝ) < 25 * (c i : ℝ))
  let BD : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ 4 * (m : ℝ) < 25 * rowEntropy (rho i))
  let G : Finset (Fin m) := Finset.univ \ (BC ∪ BD)
  have hBC : 4 * BC.card ≤ m :=
    four_mul_card_bad_codimension_le hm c hcRounds horizon
  have hBD : 4 * BD.card ≤ m :=
    four_mul_card_bad_entropy_le hm rho hrho_pos hrho_one hEntropyRounds horizon
  have hUnionCard : (BC ∪ BD).card ≤ BC.card + BD.card :=
    Finset.card_union_le BC BD
  have hUnionHalf : 2 * (BC ∪ BD).card ≤ m := by omega
  have hsubset : BC ∪ BD ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.subset_univ _
  have hcardEq : G.card + (BC ∪ BD).card = m := by
    simpa [G] using Finset.card_sdiff_add_card_eq_card hsubset
  have hGdouble : m ≤ 2 * G.card := by omega
  have hGhalf : m / 2 ≤ G.card := by omega
  refine ⟨G, hGhalf, hGdouble, ?_⟩
  intro i hi
  have hiUnion : i ∉ BC ∪ BD := (Finset.mem_sdiff.mp hi).2
  have hiBC : i ∉ BC := by
    intro hiB
    exact hiUnion (Finset.mem_union_left BD hiB)
  have hiBD : i ∉ BD := by
    intro hiB
    exact hiUnion (Finset.mem_union_right BC hiB)
  have hci : 25 * (c i : ℝ) ≤ (m : ℝ) := by
    simpa [BC, not_lt] using hiBC
  have hDi : 25 * rowEntropy (rho i) ≤ 4 * (m : ℝ) := by
    simpa [BD, not_lt] using hiBD
  obtain ⟨hdim, hkpos⟩ := dimension_high_of_good_codimension hm (hk i) hci
  have hradius := normalizedVolumeRadius_ge_exp_neg_one_sixth
    hm (hk i) (hrho_pos i) hci hDi
  exact ⟨hci, hdim, hkpos, hradius,
    one_half_lt_exp_neg_one_sixth.trans_le hradius⟩

/-- Specialization to arbitrary final row bodies satisfying the exact three
budgets exposed by `oracleRun_final_budgets`. -/
theorem many_good_final_rows {m T : ℕ} (hm : 0 < m)
    (rows : Fin m → RowBody m) (c : Fin m → ℕ)
    (hdim : ∀ i, (rows i).dim = m - c i)
    (hcRounds : ∑ i, c i ≤ T)
    (hEntropyRounds :
      ∑ i, rowEntropy ((rows i).normalizedVolume) ≤
        (T : ℝ) * entropyScale m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    ∃ G : Finset (Fin m),
      m / 2 ≤ G.card ∧ m ≤ 2 * G.card ∧
      ∀ i ∈ G,
        25 * (c i : ℝ) ≤ (m : ℝ) ∧
        24 * m ≤ 25 * (rows i).dim ∧
        0 < (rows i).dim ∧
        Real.exp (-(1 : ℝ) / 6) ≤
          (rows i).normalizedVolume ^ (((rows i).dim : ℝ)⁻¹) ∧
        (1 / 2 : ℝ) <
          (rows i).normalizedVolume ^ (((rows i).dim : ℝ)⁻¹) := by
  exact many_good_rows_of_round_budgets hm c (fun i ↦ (rows i).dim)
    (fun i ↦ (rows i).normalizedVolume) hdim
    (fun i ↦ (rows i).normalizedVolume_pos hm)
    (fun i ↦ (rows i).normalizedVolume_le_one hm)
    hcRounds hEntropyRounds horizon

/-- End-to-end specialization to the concrete resisting-oracle trajectory. -/
theorem oracleRun_many_good_rows {m T : ℕ} [NeZero m]
    (A : DeterministicStrategy m)
    (horizon : (T : ℝ) ≤
      (1 / 100 : ℝ) * (m : ℝ) ^ 2 / paperLog m) :
    ∃ G : Finset (Fin m),
      m / 2 ≤ G.card ∧ m ≤ 2 * G.card ∧
      ∀ i ∈ G,
        25 * (oracleRowCount A T i : ℝ) ≤ (m : ℝ) ∧
        24 * m ≤ 25 * ((oracleStateAt A T).rows i).dim ∧
        0 < ((oracleStateAt A T).rows i).dim ∧
        Real.exp (-(1 : ℝ) / 6) ≤
          ((oracleStateAt A T).rows i).normalizedVolume ^
            ((((oracleStateAt A T).rows i).dim : ℝ)⁻¹) ∧
        (1 / 2 : ℝ) <
          ((oracleStateAt A T).rows i).normalizedVolume ^
            ((((oracleStateAt A T).rows i).dim : ℝ)⁻¹) := by
  obtain ⟨hdim, hc, hD⟩ := oracleRun_final_budgets (T := T) A
  exact many_good_final_rows (Nat.pos_of_ne_zero (NeZero.ne m))
    (oracleStateAt A T).rows (oracleRowCount A T) hdim hc hD horizon

end ZeroOrderBounds.AccuracyImprovement
