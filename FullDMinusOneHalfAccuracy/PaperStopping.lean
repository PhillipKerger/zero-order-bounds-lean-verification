import FullDMinusOneHalfAccuracy.OddMain
import FullDMinusOneHalfAccuracy.ScaledMain

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# At-most-query forms of the odd-dimensional and scaled lower bounds

The public odd-dimensional and radius/Lipschitz endpoints are stated for a
fixed number of exact-value queries.  This file supplies the corresponding
transcript-dependent stopping models.  A stopping rule may inspect arbitrary
exact real answers and is required only to stop on every transcript of length
`N`.

The bookkeeping which locates the first stopped prefix is independent of the
query space, so it is factored through `TranscriptStopRule`.  The two typed
strategy models below then prove separately that exact consistency restricts
to this prefix.  Padding changes no query, and its output is literally the
stopping algorithm's output on the first terminal prefix.
-/

noncomputable section

open Metric

namespace ZeroOrderBounds.AccuracyImprovement

/-! ## Query-space-independent terminal-prefix bookkeeping -/

/-- A Boolean stopping rule on exact-real transcripts, forced to stop at
length `N`.  No regularity or computability restriction is imposed. -/
structure TranscriptStopRule (N : ℕ) where
  stop : List ℝ → Bool
  stop_at_bound : ∀ ys : List ℝ, ys.length = N → stop ys = true

namespace TranscriptStopRule

variable {N : ℕ}

/-- A terminal transcript is the first prefix on which the rule stops. -/
def IsTerminalTranscript (r : TranscriptStopRule N) (ys : List ℝ) : Prop :=
  ys.length ≤ N ∧
    r.stop ys = true ∧
    ∀ t : ℕ, t < ys.length → r.stop (ys.take t) ≠ true

/-- Canonically extend an arbitrary list to a transcript of length `N`. -/
def completeTranscript (N : ℕ) (ys : List ℝ) : List ℝ :=
  ys.take N ++ List.replicate (N - (ys.take N).length) 0

@[simp]
theorem length_completeTranscript (N : ℕ) (ys : List ℝ) :
    (completeTranscript N ys).length = N := by
  simp only [completeTranscript, List.length_append, List.length_replicate,
    List.length_take]
  omega

theorem completeTranscript_eq_self {ys : List ℝ} (hys : ys.length = N) :
    completeTranscript N ys = ys := by
  subst N
  simp [completeTranscript]

theorem exists_stopped_prefix (r : TranscriptStopRule N) (ys : List ℝ) :
    ∃ t : ℕ, t ≤ N ∧
      r.stop ((completeTranscript N ys).take t) = true := by
  refine ⟨N, le_rfl, ?_⟩
  have hstop := r.stop_at_bound (completeTranscript N ys)
    (length_completeTranscript N ys)
  have htake : (completeTranscript N ys).take N = completeTranscript N ys :=
    (List.take_eq_self_iff _).mpr (by simp)
  rwa [htake]

/-- The first stopped prefix of the canonical length-`N` completion. -/
def firstStopIndex (r : TranscriptStopRule N) (ys : List ℝ) : ℕ :=
  Nat.find (r.exists_stopped_prefix ys)

theorem firstStopIndex_spec (r : TranscriptStopRule N) (ys : List ℝ) :
    r.firstStopIndex ys ≤ N ∧
      r.stop ((completeTranscript N ys).take (r.firstStopIndex ys)) = true :=
  Nat.find_spec (r.exists_stopped_prefix ys)

theorem firstStopIndex_le (r : TranscriptStopRule N) (ys : List ℝ) :
    r.firstStopIndex ys ≤ N :=
  (r.firstStopIndex_spec ys).1

theorem not_stop_before_firstStopIndex (r : TranscriptStopRule N)
    (ys : List ℝ) {t : ℕ} (ht : t < r.firstStopIndex ys) :
    r.stop ((completeTranscript N ys).take t) ≠ true := by
  intro hstop
  exact Nat.find_min (r.exists_stopped_prefix ys) ht
    ⟨le_trans (Nat.le_of_lt ht) (r.firstStopIndex_le ys), hstop⟩

/-- The actual transcript on which the rule first stops. -/
def terminalPrefix (r : TranscriptStopRule N) (ys : List ℝ) : List ℝ :=
  (completeTranscript N ys).take (r.firstStopIndex ys)

@[simp]
theorem length_terminalPrefix (r : TranscriptStopRule N) (ys : List ℝ) :
    (r.terminalPrefix ys).length = r.firstStopIndex ys := by
  rw [terminalPrefix, List.length_take, length_completeTranscript]
  exact Nat.min_eq_left (r.firstStopIndex_le ys)

@[simp]
theorem stop_terminalPrefix (r : TranscriptStopRule N) (ys : List ℝ) :
    r.stop (r.terminalPrefix ys) = true :=
  (r.firstStopIndex_spec ys).2

theorem terminalPrefix_isTerminal (r : TranscriptStopRule N) (ys : List ℝ) :
    r.IsTerminalTranscript (r.terminalPrefix ys) := by
  refine ⟨?_, r.stop_terminalPrefix ys, ?_⟩
  · simpa using r.firstStopIndex_le ys
  · intro t ht
    have ht' : t < r.firstStopIndex ys := by simpa using ht
    have htake : (r.terminalPrefix ys).take t =
        (completeTranscript N ys).take t := by
      rw [terminalPrefix, List.take_take, Nat.min_eq_left (Nat.le_of_lt ht')]
    rw [htake]
    exact r.not_stop_before_firstStopIndex ys ht'

theorem terminalPrefix_eq_take {ys : List ℝ} (r : TranscriptStopRule N)
    (hys : ys.length = N) :
    r.terminalPrefix ys = ys.take (r.firstStopIndex ys) := by
  rw [terminalPrefix, completeTranscript_eq_self hys]

end TranscriptStopRule

/-! ## Ambient Euclidean stopping strategies -/

/-- A deterministic exact-value strategy on the ambient unit ball which may
stop after seeing any transcript, but must stop by query `N`. -/
structure AmbientStoppingStrategy (d N : ℕ) where
  query : List ℝ → AmbientUnitBall d
  output : List ℝ → AmbientUnitBall d
  stop : List ℝ → Bool
  stop_at_bound : ∀ ys : List ℝ, ys.length = N → stop ys = true

namespace AmbientStoppingStrategy

variable {d N : ℕ}

def stopRule (B : AmbientStoppingStrategy d N) : TranscriptStopRule N where
  stop := B.stop
  stop_at_bound := B.stop_at_bound

def underlying (B : AmbientStoppingStrategy d N) :
    AmbientDeterministicStrategy d where
  query := B.query
  output := B.output

def IsTerminalTranscript (B : AmbientStoppingStrategy d N)
    (ys : List ℝ) : Prop :=
  B.stopRule.IsTerminalTranscript ys

def firstStopIndex (B : AmbientStoppingStrategy d N) (ys : List ℝ) : ℕ :=
  B.stopRule.firstStopIndex ys

def terminalPrefix (B : AmbientStoppingStrategy d N) (ys : List ℝ) : List ℝ :=
  B.stopRule.terminalPrefix ys

@[simp]
theorem length_terminalPrefix (B : AmbientStoppingStrategy d N)
    (ys : List ℝ) :
    (B.terminalPrefix ys).length = B.firstStopIndex ys :=
  B.stopRule.length_terminalPrefix ys

theorem terminalPrefix_isTerminal (B : AmbientStoppingStrategy d N)
    (ys : List ℝ) :
    B.IsTerminalTranscript (B.terminalPrefix ys) :=
  B.stopRule.terminalPrefix_isTerminal ys

theorem terminalPrefix_eq_take {ys : List ℝ}
    (B : AmbientStoppingStrategy d N) (hys : ys.length = N) :
    B.terminalPrefix ys = ys.take (B.firstStopIndex ys) :=
  B.stopRule.terminalPrefix_eq_take hys

/-- Padding retains every query and ignores answers following the first
terminal prefix when producing the output. -/
def pad (B : AmbientStoppingStrategy d N) : AmbientDeterministicStrategy d where
  query := B.query
  output := fun ys ↦ B.output (B.terminalPrefix ys)

@[simp]
theorem pad_query (B : AmbientStoppingStrategy d N) (ys : List ℝ) :
    B.pad.query ys = B.query ys := rfl

@[simp]
theorem pad_output (B : AmbientStoppingStrategy d N) (ys : List ℝ) :
    B.pad.output ys = B.output (B.terminalPrefix ys) := rfl

theorem consistent_pad_iff_underlying (B : AmbientStoppingStrategy d N)
    (ys : List ℝ) (f : AmbientQuerySpace d → ℝ) :
    AmbientConsistent B.pad ys f ↔ AmbientConsistent B.underlying ys f := by
  rfl

/-- Ambient exact consistency is inherited by every prefix. -/
theorem consistent_take {A : AmbientDeterministicStrategy d}
    {ys : List ℝ} {f : AmbientQuerySpace d → ℝ}
    (h : AmbientConsistent A ys f) (n : ℕ) :
    AmbientConsistent A (ys.take n) f := by
  intro t ht
  have htmin : t < min n ys.length := by simpa using ht
  have htn : t ≤ n := Nat.le_of_lt (htmin.trans_le (min_le_left _ _))
  have hty : t < ys.length := htmin.trans_le (min_le_right _ _)
  have hv := h t hty
  have hquery : A.queryAt (ys.take n) t = A.queryAt ys t := by
    simp [AmbientDeterministicStrategy.queryAt, List.take_take,
      Nat.min_eq_left htn]
  rw [hquery, hv]
  exact List.getElem_take.symm

/-- A consistent full padded transcript restricts to a consistent genuine
terminal transcript. -/
theorem consistent_terminalPrefix (B : AmbientStoppingStrategy d N)
    {ys : List ℝ} {f : AmbientQuerySpace d → ℝ}
    (hys : ys.length = N) (hconsistent : AmbientConsistent B.pad ys f) :
    AmbientConsistent B.underlying (B.terminalPrefix ys) f := by
  have htake : AmbientConsistent B.pad
      (ys.take (B.firstStopIndex ys)) f :=
    consistent_take hconsistent (B.firstStopIndex ys)
  rw [B.terminalPrefix_eq_take hys]
  exact (B.consistent_pad_iff_underlying _ _).mp htake

/-- Uniform success of a particular transcript-dependent ambient strategy. -/
def SucceedsWithin (B : AmbientStoppingStrategy d N) (ε : ℝ) : Prop :=
  ∀ (ys : List ℝ) (f : AmbientQuerySpace d → ℝ)
    (xstar : AmbientQuerySpace d),
    B.IsTerminalTranscript ys →
    f 0 = 0 →
    ConvexOn ℝ Set.univ f →
    LipschitzWith 1 f →
    AmbientConsistent B.underlying ys f →
    xstar ∈ ambientUnitBall d →
    IsMinOn f (ambientUnitBall d) xstar →
    f (B.output ys : AmbientQuerySpace d) - f xstar ≤ ε

/-- Existence of an ambient strategy which succeeds and stops by `N`. -/
def AtMostSucceedsWithin (d N : ℕ) (ε : ℝ) : Prop :=
  ∃ B : AmbientStoppingStrategy d N, B.SucceedsWithin ε

theorem pad_preserves_success {B : AmbientStoppingStrategy d N} {ε : ℝ}
    (hB : B.SucceedsWithin ε) :
    ∀ (ys : List ℝ) (f : AmbientQuerySpace d → ℝ)
      (xstar : AmbientQuerySpace d),
      ys.length = N →
      f 0 = 0 →
      ConvexOn ℝ Set.univ f →
      LipschitzWith 1 f →
      AmbientConsistent B.pad ys f →
      xstar ∈ ambientUnitBall d →
      IsMinOn f (ambientUnitBall d) xstar →
      f (B.pad.output ys : AmbientQuerySpace d) - f xstar ≤ ε := by
  intro ys f xstar hys hzero hconv hlip hconsistent hxstar hmin
  exact hB (B.terminalPrefix ys) f xstar
    (B.terminalPrefix_isTerminal ys) hzero hconv hlip
    (B.consistent_terminalPrefix hys hconsistent) hxstar hmin

/-- Padding turns every successful at-most strategy into a successful
fixed-horizon strategy with exactly the same terminal output. -/
theorem ambientSucceedsWithin_of_atMostSucceedsWithin
    (h : AtMostSucceedsWithin d N ε) :
    AmbientSucceedsWithin d N ε := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B.pad, B.pad_preserves_success hB⟩

/-- A fixed-horizon ambient strategy as one which stops exactly at `N`. -/
def ofFixedHorizon (A : AmbientDeterministicStrategy d) (N : ℕ) :
    AmbientStoppingStrategy d N where
  query := A.query
  output := A.output
  stop := fun ys ↦ decide (ys.length = N)
  stop_at_bound := by
    intro ys hys
    simp [hys]

@[simp]
theorem ofFixedHorizon_underlying (A : AmbientDeterministicStrategy d)
    (N : ℕ) :
    (ofFixedHorizon A N).underlying = A := rfl

theorem ofFixedHorizon_terminal_length (A : AmbientDeterministicStrategy d)
    {ys : List ℝ}
    (hterminal : (ofFixedHorizon A N).IsTerminalTranscript ys) :
    ys.length = N := by
  exact of_decide_eq_true hterminal.2.1

theorem atMostSucceedsWithin_of_ambientSucceedsWithin
    (h : AmbientSucceedsWithin d N ε) :
    AtMostSucceedsWithin d N ε := by
  obtain ⟨A, hA⟩ := h
  refine ⟨ofFixedHorizon A N, ?_⟩
  intro ys f xstar hterminal hzero hconv hlip hconsistent hxstar hmin
  exact hA ys f xstar (ofFixedHorizon_terminal_length A hterminal)
    hzero hconv hlip hconsistent hxstar hmin

theorem atMostSucceedsWithin_iff_ambientSucceedsWithin (ε : ℝ) :
    AtMostSucceedsWithin d N ε ↔ AmbientSucceedsWithin d N ε :=
  ⟨ambientSucceedsWithin_of_atMostSucceedsWithin,
    atMostSucceedsWithin_of_ambientSucceedsWithin⟩

end AmbientStoppingStrategy

/-! ## Radius/Lipschitz stopping strategies -/

/-- A radius-`R` exact-value strategy with a transcript-dependent stop rule
and a hard upper bound of `N` queries. -/
structure RadiusStoppingStrategy (m N : ℕ) (R : ℝ) where
  query : List ℝ → RadiusBall m R
  output : List ℝ → RadiusBall m R
  stop : List ℝ → Bool
  stop_at_bound : ∀ ys : List ℝ, ys.length = N → stop ys = true

namespace RadiusStoppingStrategy

variable {m N : ℕ} {R : ℝ}

def stopRule (B : RadiusStoppingStrategy m N R) : TranscriptStopRule N where
  stop := B.stop
  stop_at_bound := B.stop_at_bound

def underlying (B : RadiusStoppingStrategy m N R) :
    RadiusDeterministicStrategy m R where
  query := B.query
  output := B.output

def IsTerminalTranscript (B : RadiusStoppingStrategy m N R)
    (ys : List ℝ) : Prop :=
  B.stopRule.IsTerminalTranscript ys

def firstStopIndex (B : RadiusStoppingStrategy m N R) (ys : List ℝ) : ℕ :=
  B.stopRule.firstStopIndex ys

def terminalPrefix (B : RadiusStoppingStrategy m N R)
    (ys : List ℝ) : List ℝ :=
  B.stopRule.terminalPrefix ys

@[simp]
theorem length_terminalPrefix (B : RadiusStoppingStrategy m N R)
    (ys : List ℝ) :
    (B.terminalPrefix ys).length = B.firstStopIndex ys :=
  B.stopRule.length_terminalPrefix ys

theorem terminalPrefix_isTerminal (B : RadiusStoppingStrategy m N R)
    (ys : List ℝ) :
    B.IsTerminalTranscript (B.terminalPrefix ys) :=
  B.stopRule.terminalPrefix_isTerminal ys

theorem terminalPrefix_eq_take {ys : List ℝ}
    (B : RadiusStoppingStrategy m N R) (hys : ys.length = N) :
    B.terminalPrefix ys = ys.take (B.firstStopIndex ys) :=
  B.stopRule.terminalPrefix_eq_take hys

/-- Fixed-horizon padding of a radius-`R` stopping strategy. -/
def pad (B : RadiusStoppingStrategy m N R) :
    RadiusDeterministicStrategy m R where
  query := B.query
  output := fun ys ↦ B.output (B.terminalPrefix ys)

@[simp]
theorem pad_query (B : RadiusStoppingStrategy m N R) (ys : List ℝ) :
    B.pad.query ys = B.query ys := rfl

@[simp]
theorem pad_output (B : RadiusStoppingStrategy m N R) (ys : List ℝ) :
    B.pad.output ys = B.output (B.terminalPrefix ys) := rfl

theorem consistent_pad_iff_underlying [NeZero m]
    (B : RadiusStoppingStrategy m N R) (ys : List ℝ) (W : RowMatrix m)
    (L : ℝ) :
    RadiusConsistent B.pad ys (scaledHardObjective R L W) ↔
      RadiusConsistent B.underlying ys (scaledHardObjective R L W) := by
  rfl

/-- Radius-model exact consistency is inherited by every prefix. -/
theorem consistent_take {A : RadiusDeterministicStrategy m R}
    {ys : List ℝ} {f : QuerySpace m → ℝ}
    (h : RadiusConsistent A ys f) (n : ℕ) :
    RadiusConsistent A (ys.take n) f := by
  intro t ht
  have htmin : t < min n ys.length := by simpa using ht
  have htn : t ≤ n := Nat.le_of_lt (htmin.trans_le (min_le_left _ _))
  have hty : t < ys.length := htmin.trans_le (min_le_right _ _)
  have hv := h t hty
  have hquery : A.queryAt (ys.take n) t = A.queryAt ys t := by
    simp [RadiusDeterministicStrategy.queryAt, List.take_take,
      Nat.min_eq_left htn]
  rw [hquery, hv]
  exact List.getElem_take.symm

theorem consistent_terminalPrefix [NeZero m]
    (B : RadiusStoppingStrategy m N R)
    {ys : List ℝ} {W : RowMatrix m} {L : ℝ}
    (hys : ys.length = N)
    (hconsistent : RadiusConsistent B.pad ys (scaledHardObjective R L W)) :
    RadiusConsistent B.underlying (B.terminalPrefix ys)
      (scaledHardObjective R L W) := by
  have htake : RadiusConsistent B.pad
      (ys.take (B.firstStopIndex ys)) (scaledHardObjective R L W) :=
    consistent_take hconsistent (B.firstStopIndex ys)
  rw [B.terminalPrefix_eq_take hys]
  exact (B.consistent_pad_iff_underlying _ _ _).mp htake

/-- Uniform success of a stopping strategy on the scaled hard family. -/
def SucceedsWithin (B : RadiusStoppingStrategy m N R) [NeZero m]
    (L ε : ℝ) : Prop :=
  ∀ (ys : List ℝ) (W : RowMatrix m),
    B.IsTerminalTranscript ys →
    Admissible W →
    RadiusConsistent B.underlying ys (scaledHardObjective R L W) →
    scaledHardObjective R L W (B.output ys : QuerySpace m) -
        scaledHardObjective R L W (scaledHardOptimizer R W) ≤ ε

/-- Existence of a radius-`R` strategy succeeding after at most `N` queries. -/
def AtMostSucceedsWithin (m N : ℕ) [NeZero m]
    (R L ε : ℝ) : Prop :=
  ∃ B : RadiusStoppingStrategy m N R, B.SucceedsWithin L ε

theorem pad_preserves_success [NeZero m]
    {B : RadiusStoppingStrategy m N R} {L ε : ℝ}
    (hB : B.SucceedsWithin L ε) :
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = N →
      Admissible W →
      RadiusConsistent B.pad ys (scaledHardObjective R L W) →
      scaledHardObjective R L W (B.pad.output ys : QuerySpace m) -
          scaledHardObjective R L W (scaledHardOptimizer R W) ≤ ε := by
  intro ys W hys hW hconsistent
  exact hB (B.terminalPrefix ys) W (B.terminalPrefix_isTerminal ys) hW
    (B.consistent_terminalPrefix hys hconsistent)

theorem radiusSucceedsWithin_of_atMostSucceedsWithin [NeZero m]
    (h : AtMostSucceedsWithin m N R L ε) :
    RadiusSucceedsWithin m N R L ε := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B.pad, B.pad_preserves_success hB⟩

/-- A fixed-horizon radius strategy stops exactly at `N`. -/
def ofFixedHorizon (A : RadiusDeterministicStrategy m R) (N : ℕ) :
    RadiusStoppingStrategy m N R where
  query := A.query
  output := A.output
  stop := fun ys ↦ decide (ys.length = N)
  stop_at_bound := by
    intro ys hys
    simp [hys]

@[simp]
theorem ofFixedHorizon_underlying (A : RadiusDeterministicStrategy m R)
    (N : ℕ) :
    (ofFixedHorizon A N).underlying = A := rfl

theorem ofFixedHorizon_terminal_length
    (A : RadiusDeterministicStrategy m R) {ys : List ℝ}
    (hterminal : (ofFixedHorizon A N).IsTerminalTranscript ys) :
    ys.length = N := by
  exact of_decide_eq_true hterminal.2.1

theorem atMostSucceedsWithin_of_radiusSucceedsWithin [NeZero m]
    (h : RadiusSucceedsWithin m N R L ε) :
    AtMostSucceedsWithin m N R L ε := by
  obtain ⟨A, hA⟩ := h
  refine ⟨ofFixedHorizon A N, ?_⟩
  intro ys W hterminal hW hconsistent
  exact hA ys W (ofFixedHorizon_terminal_length A hterminal) hW hconsistent

theorem atMostSucceedsWithin_iff_radiusSucceedsWithin [NeZero m]
    (R L ε : ℝ) :
    AtMostSucceedsWithin m N R L ε ↔ RadiusSucceedsWithin m N R L ε :=
  ⟨radiusSucceedsWithin_of_atMostSucceedsWithin,
    atMostSucceedsWithin_of_radiusSucceedsWithin⟩

end RadiusStoppingStrategy

/-! ## Unconditional odd-dimensional at-most-query endpoint -/

/-- No ambient algorithm which stops transcript-dependently by `T` succeeds
at the odd-dimensional paper accuracy, for any `T` below the canonical
integer budget. -/
theorem not_ambientAtMostSucceedsWithin_oddSqrtAccuracy_of_le_paperQueryBudget
    {m T : ℕ} [NeZero m] (hT : T ≤ paperQueryBudget m) :
    ¬ AmbientStoppingStrategy.AtMostSucceedsWithin
      (2 * m + 1) T (oddSqrtAccuracy m) := by
  intro hstop
  exact not_ambientSucceedsWithin_oddSqrtAccuracy_of_le_paperQueryBudget hT
    (AmbientStoppingStrategy.ambientSucceedsWithin_of_atMostSucceedsWithin hstop)

/-- Canonical-budget odd-dimensional at-most-query impossibility. -/
theorem not_ambientAtMostPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy
    {m : ℕ} [NeZero m] :
    ¬ AmbientStoppingStrategy.AtMostSucceedsWithin
      (2 * m + 1) (paperQueryBudget m) (oddSqrtAccuracy m) :=
  not_ambientAtMostSucceedsWithin_oddSqrtAccuracy_of_le_paperQueryBudget le_rfl

/-- Audit-facing odd-dimensional stopping result, paired with the explicit
`d² / (1800 log(d+1))` lower-rate certificate. -/
theorem
    not_ambientAtMostPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy_and_rate
    {m : ℕ} [NeZero m] :
    (¬ AmbientStoppingStrategy.AtMostSucceedsWithin
        (2 * m + 1) (paperQueryBudget m) (oddSqrtAccuracy m)) ∧
      ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
          (1800 * Real.log ((2 * m + 2 : ℕ) : ℝ)) <
        ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact ⟨not_ambientAtMostPaperQueryBudgetSucceedsWithin_oddSqrtAccuracy,
    paperQueryBudget_succ_gt_odd_dimension_log_succ_rate
      (Nat.pos_of_ne_zero (NeZero.ne m))⟩

/-! ## Unconditional scaled at-most-query endpoint -/

/-- On a radius-`R` ball, no transcript-dependent algorithm stopping by `T`
succeeds at any accuracy `ε ≤ L R · sqrtAccuracy m`, whenever `T` is within
the paper budget. -/
theorem not_radiusAtMostSucceedsWithin_of_le_sqrtAccuracy_of_le_paperQueryBudget
    {m T : ℕ} [NeZero m] {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hε : ε ≤ (L * R) * sqrtAccuracy m)
    (hT : T ≤ paperQueryBudget m) :
    ¬ RadiusStoppingStrategy.AtMostSucceedsWithin m T R L ε := by
  intro hstop
  apply not_radiusSucceedsWithin_of_le_sqrtAccuracy hR hL hε
  · exact horizon_of_le_paperQueryBudget
      (Nat.pos_of_ne_zero (NeZero.ne m)) hT
  · exact RadiusStoppingStrategy.radiusSucceedsWithin_of_atMostSucceedsWithin
      hstop

/-- Canonical-budget scaled impossibility at the exact `L R / sqrt(d)`
threshold. -/
theorem not_radiusAtMostPaperQueryBudgetSucceedsWithinSqrt
    {m : ℕ} [NeZero m] {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) :
    ¬ RadiusStoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
      R L ((L * R) * sqrtAccuracy m) :=
  not_radiusAtMostSucceedsWithin_of_le_sqrtAccuracy_of_le_paperQueryBudget
    hR hL le_rfl le_rfl

/-- Canonical-budget monotone form, retaining an arbitrary requested accuracy
below the scaled paper threshold. -/
theorem
    not_radiusAtMostPaperQueryBudgetSucceedsWithin_of_le_sqrtAccuracy
    {m : ℕ} [NeZero m] {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hε : ε ≤ (L * R) * sqrtAccuracy m) :
    ¬ RadiusStoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
      R L ε :=
  not_radiusAtMostSucceedsWithin_of_le_sqrtAccuracy_of_le_paperQueryBudget
    hR hL hε le_rfl

/-- The canonical scaled at-most-query impossibility together with the same
explicit even-dimensional quadratic-over-logarithmic budget certificate. -/
theorem not_radiusAtMostPaperQueryBudgetSucceedsWithinSqrt_and_rate
    {m : ℕ} [NeZero m] {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) :
    (¬ RadiusStoppingStrategy.AtMostSucceedsWithin m (paperQueryBudget m)
        R L ((L * R) * sqrtAccuracy m)) ∧
      (2 * (m : ℝ)) ^ 2 /
          (800 * Real.log ((2 * m + 1 : ℕ) : ℝ)) <
        ((paperQueryBudget m + 1 : ℕ) : ℝ) := by
  exact ⟨not_radiusAtMostPaperQueryBudgetSucceedsWithinSqrt hR hL,
    paperQueryBudget_succ_gt_even_dimension_log_succ_rate
      (Nat.pos_of_ne_zero (NeZero.ne m))⟩

end ZeroOrderBounds.AccuracyImprovement
