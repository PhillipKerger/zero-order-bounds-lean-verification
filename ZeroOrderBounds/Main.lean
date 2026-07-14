import ZeroOrderBounds.VolumePotential
import ZeroOrderBounds.Indistinguishability
import ZeroOrderBounds.OracleRun

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Final lower-bound assembly

This file assembles the potential/good-row conclusion with the exact product
invariant and the one-row sensitivity theorem.  The first theorem is phrased
for an arbitrary final oracle state together with its certified codimension and
entropy budgets.  The oracle iterator supplies exactly these hypotheses.
-/

noncomputable section

open Metric
open scoped BigOperators

namespace ZeroOrderBounds

/-- A final state satisfying the two global budgets already defeats the
strategy at the advertised accuracy. -/
theorem exists_advertised_gap_of_final_budgets
    {m : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (A : DeterministicStrategy m) (S : OracleState A)
    (c : Fin m → ℕ)
    (hdim : ∀ i, (S.rows i).dim = m - c i)
    (hcBudget : 1000 * ∑ i, (c i : ℝ) ≤ (m : ℝ) ^ 2)
    (hEntropyBudget :
      1000 * ∑ i, rowEntropy ((S.rows i).normalizedVolume) ≤
        (m : ℝ) ^ 2 * entropyScale m) :
    ∃ W : RowMatrix m,
      W ∈ rowProduct S.rows ∧
      Consistent A S.answers W ∧
      1 / (200000000 * (m : ℝ) ^ 3) <
        hardObjective W (A.output S.answers : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  have hmPos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  let rho : Fin m → ℝ := fun i ↦ (S.rows i).normalizedVolume
  have hrhoPos : ∀ i, 0 < rho i := fun i ↦ (S.rows i).normalizedVolume_pos hmPos
  have hrhoOne : ∀ i, rho i ≤ 1 := fun i ↦ (S.rows i).normalizedVolume_le_one hmPos
  obtain ⟨i, hcdiv, hdimLarge, _hentropy, hpower, _hroot⟩ :=
    exists_good_row_quarter_radius hm c rho hrhoPos hrhoOne hcBudget
      (by simpa [rho] using hEntropyBudget)
  have hkPos : 0 < m - c i := by
    have hm99 : 0 < 99 * m := Nat.mul_pos (by norm_num) hmPos
    omega
  have hbodyDim : 0 < (S.rows i).body.dim := by
    rw [← RowBody.dim, hdim i]
    exact hkPos
  have hnormalizer :
      0 < kappaReal (S.rows i).dim * tau m ^ (S.rows i).dim :=
    (S.rows i).normalizer_pos hmPos
  have hvolume :
      (S.rows i).body.volumeReal =
        kappaReal (S.rows i).body.dim * tau m ^ (S.rows i).body.dim * rho i := by
    change (S.rows i).volumeReal =
      kappaReal (S.rows i).dim * tau m ^ (S.rows i).dim *
        (S.rows i).normalizedVolume
    rw [RowBody.normalizedVolume]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnormalizer.ne']
  have hpowerBody :
      (m : ℝ) ^ (-((S.rows i).body.dim : ℝ) / 4) ≤ rho i := by
    rw [show (S.rows i).body.dim = m - c i by exact hdim i]
    simpa using hpower
  obtain ⟨w, hw, w', hw', hsep⟩ :=
    (S.rows i).body.exists_pair_dist_ge_quarter hmPos hbodyDim (tau_pos hmPos)
      hvolume hpowerBody
  exact S.exists_consistent_selection_with_advertised_gap i hw hw' hsep

/-- Round-count form of the final-state theorem, matching the direct output of
the oracle iterator and volume-potential theorem. -/
theorem exists_advertised_gap_of_round_budgets
    {m T : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (horizon : 1000 * T ≤ m ^ 2)
    (A : DeterministicStrategy m) (S : OracleState A)
    (c : Fin m → ℕ)
    (hdim : ∀ i, (S.rows i).dim = m - c i)
    (hcRounds : ∑ i, c i ≤ T)
    (hEntropyRounds :
      ∑ i, rowEntropy ((S.rows i).normalizedVolume) ≤
        (T : ℝ) * entropyScale m) :
    ∃ W : RowMatrix m,
      W ∈ rowProduct S.rows ∧
      Consistent A S.answers W ∧
      1 / (200000000 * (m : ℝ) ^ 3) <
        hardObjective W (A.output S.answers : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  have hmPos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hL : 0 ≤ entropyScale m := (entropyScale_pos (by omega)).le
  have horizonR : (1000 : ℝ) * (T : ℝ) ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast horizon
  have hcRoundsR : ∑ i, (c i : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hcRounds
  have hcBudget :
      1000 * ∑ i, (c i : ℝ) ≤ (m : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcRoundsR (by norm_num)).trans horizonR
  have hEntropyBudget :
      1000 * ∑ i, rowEntropy ((S.rows i).normalizedVolume) ≤
        (m : ℝ) ^ 2 * entropyScale m := by
    calc
      1000 * ∑ i, rowEntropy ((S.rows i).normalizedVolume) ≤
          1000 * ((T : ℝ) * entropyScale m) :=
        mul_le_mul_of_nonneg_left hEntropyRounds (by norm_num)
      _ = ((1000 : ℝ) * T) * entropyScale m := by ring
      _ ≤ (m : ℝ) ^ 2 * entropyScale m :=
        mul_le_mul_of_nonneg_right horizonR hL
  exact exists_advertised_gap_of_final_budgets hm A S c hdim hcBudget hEntropyBudget

/-! ## Public fixed-horizon theorem -/

/-- The strict form of the fixed-horizon lower bound.

For every deterministic exact-value strategy and every horizon satisfying
`1000 * T ≤ m²`, the resisting oracle produces exactly `T` answers and an
admissible hard max-affine objective reproducing all of them.  The displayed
point is a genuine minimizer on the Euclidean unit ball, and the strategy's
output has error strictly larger than the advertised threshold.

The `NeZero m` instance is logically redundant under `1000 ≤ m`; it is kept as
an implicit parameter because the finite maximum defining `hardObjective`
uses nonemptiness of `Fin m` at the type level. -/
theorem fixedHorizonLowerBound_strict
    {m T : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (horizon : 1000 * T ≤ m ^ 2)
    (A : DeterministicStrategy m) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      Consistent A ys W ∧
      hardOptimizer W ∈ unitBall m ∧
      IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) ∧
      1 / (200000000 * (m : ℝ) ^ 3) <
        hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  let S : OracleState A := oracleStateAt A T
  let c : Fin m → ℕ := oracleRowCount A T
  obtain ⟨hdim, hcRounds, hEntropyRounds⟩ :=
    oracleRun_final_budgets (T := T) A
  obtain ⟨W, hW, hconsistent, hgap⟩ :=
    exists_advertised_gap_of_round_budgets hm horizon A S c
      (by simpa [S, c] using hdim)
      (by simpa [c] using hcRounds)
      (by simpa [S] using hEntropyRounds)
  refine ⟨S.answers, W, ?_, admissible_of_mem_rowProduct hW,
    hconsistent, hardOptimizer_mem_unitBall W, hardOptimizer_isMinOn W, hgap⟩
  simp [S]

/-- Requested non-strict form of the fixed-horizon lower bound.  The strict
theorem above is retained because it directly yields the no-strategy
corollary at the same numerical accuracy. -/
theorem fixedHorizonLowerBound
    {m T : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (horizon : 1000 * T ≤ m ^ 2)
    (A : DeterministicStrategy m) :
    ∃ ys : List ℝ, ∃ W : RowMatrix m,
      ys.length = T ∧
      Admissible W ∧
      Consistent A ys W ∧
      hardOptimizer W ∈ unitBall m ∧
      IsMinOn (hardObjective W) (unitBall m) (hardOptimizer W) ∧
      1 / (200000000 * (m : ℝ) ^ 3) ≤
        hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) := by
  obtain ⟨ys, W, hlen, hW, hconsistent, hoptimizer, hmin, hgap⟩ :=
    fixedHorizonLowerBound_strict hm horizon A
  exact ⟨ys, W, hlen, hW, hconsistent, hoptimizer, hmin, hgap.le⟩

/-- A fixed-horizon strategy succeeds at accuracy `ε` when its output has
error at most `ε` for every admissible hard instance and every exact
length-`T` transcript consistent with that instance.  This is the padded
fixed-horizon model described in the formalization plan. -/
def SucceedsWithin (m T : ℕ) [NeZero m] (ε : ℝ) : Prop :=
  ∃ A : DeterministicStrategy m,
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = T →
      Admissible W →
      Consistent A ys W →
      hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) ≤ ε

/-- No deterministic exact-value strategy succeeds at the advertised
accuracy within a horizon satisfying `1000 * T ≤ m²`. -/
theorem not_succeedsWithin_advertised
    {m T : ℕ} [NeZero m] (hm : 1000 ≤ m)
    (horizon : 1000 * T ≤ m ^ 2) :
    ¬SucceedsWithin m T (1 / (200000000 * (m : ℝ) ^ 3)) := by
  rintro ⟨A, hA⟩
  obtain ⟨ys, W, hlen, hW, hconsistent, _hoptimizer, _hmin, hgap⟩ :=
    fixedHorizonLowerBound_strict hm horizon A
  exact (not_lt_of_ge (hA ys W hlen hW hconsistent)) hgap

#print axioms fixedHorizonLowerBound_strict
#print axioms fixedHorizonLowerBound
#print axioms not_succeedsWithin_advertised

end ZeroOrderBounds
