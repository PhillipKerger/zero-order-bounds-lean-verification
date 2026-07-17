import FullDMinusOneHalfAccuracy.Statement

-- This repository has not selected a source license or named copyright holder yet.
set_option linter.style.header false

/-!
# Transcript-dependent stopping and fixed-horizon padding

The lower-bound proof is most naturally stated for a strategy that makes exactly
`N` queries.  A usual oracle algorithm may instead stop after inspecting the
answers received so far.  This file gives a precise deterministic model for
such algorithms and proves that, as far as worst-case success is concerned,
the at-most-`N` and exactly-`N` models are equivalent.

A `StoppingStrategy m N` has a Boolean stopping decision at every transcript.
The field `stop_at_bound` says that it must stop on every length-`N`
transcript.  Thus no measurability, continuity, or computability assumption is
hidden in the model.  A terminal transcript is the *first* prefix on which the
stopping decision is true.

To pad a stopping strategy, we retain its query rule for all `N` rounds and
make the fixed-horizon output equal to its output on the first stopped prefix.
Queries after that prefix are fictitious padding queries.  Their values cannot
affect the output, and consistency of the full transcript implies consistency
of the genuine prefix.  This is exactly what is needed to transfer a uniform
success guarantee to the existing `DeterministicStrategy` model.
-/

noncomputable section

namespace ZeroOrderBounds.AccuracyImprovement

open ZeroOrderBounds

/-! ## Stopping strategies and terminal transcripts -/

/-- A deterministic exact-value strategy which must stop after at most `N`
queries.  The stopping decision is allowed to depend on the entire exact
transcript seen so far. -/
structure StoppingStrategy (m N : ℕ) where
  query : List ℝ → UnitBall m
  output : List ℝ → UnitBall m
  stop : List ℝ → Bool
  stop_at_bound : ∀ ys : List ℝ, ys.length = N → stop ys = true

namespace StoppingStrategy

variable {m N : ℕ}

/-- Forget the stopping rule.  This strategy describes all genuine queries
before stopping; its output map is also useful when stating prefix
consistency. -/
def underlying (B : StoppingStrategy m N) : DeterministicStrategy m where
  query := B.query
  output := B.output

@[simp]
theorem underlying_query (B : StoppingStrategy m N) (ys : List ℝ) :
    B.underlying.query ys = B.query ys := rfl

@[simp]
theorem underlying_output (B : StoppingStrategy m N) (ys : List ℝ) :
    B.underlying.output ys = B.output ys := rfl

/-- A terminal transcript is a transcript of length at most `N` on which the
strategy stops for the first time. -/
def IsTerminalTranscript (B : StoppingStrategy m N) (ys : List ℝ) : Prop :=
  ys.length ≤ N ∧
    B.stop ys = true ∧
    ∀ t : ℕ, t < ys.length → B.stop (ys.take t) ≠ true

/-- Extend an arbitrary list canonically to length `N`.  Only the behavior on
already length-`N` lists is semantically relevant; totality makes the padded
strategy an ordinary `DeterministicStrategy`. -/
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

/-- There is a stopped prefix of the canonical length-`N` completion. -/
theorem exists_stopped_prefix (B : StoppingStrategy m N) (ys : List ℝ) :
    ∃ t : ℕ, t ≤ N ∧
      B.stop ((completeTranscript N ys).take t) = true := by
  refine ⟨N, le_rfl, ?_⟩
  have hstop := B.stop_at_bound (completeTranscript N ys)
    (length_completeTranscript N ys)
  have htake : (completeTranscript N ys).take N = completeTranscript N ys :=
    (List.take_eq_self_iff _).mpr (by simp)
  rw [htake]
  exact hstop

/-- The first time at which `B` stops on the canonical completion of `ys`. -/
def firstStopIndex (B : StoppingStrategy m N) (ys : List ℝ) : ℕ :=
  Nat.find (B.exists_stopped_prefix ys)

theorem firstStopIndex_spec (B : StoppingStrategy m N) (ys : List ℝ) :
    B.firstStopIndex ys ≤ N ∧
      B.stop ((completeTranscript N ys).take (B.firstStopIndex ys)) = true :=
  Nat.find_spec (B.exists_stopped_prefix ys)

theorem firstStopIndex_le (B : StoppingStrategy m N) (ys : List ℝ) :
    B.firstStopIndex ys ≤ N :=
  (B.firstStopIndex_spec ys).1

theorem stop_firstStopIndex (B : StoppingStrategy m N) (ys : List ℝ) :
    B.stop ((completeTranscript N ys).take (B.firstStopIndex ys)) = true :=
  (B.firstStopIndex_spec ys).2

theorem not_stop_before_firstStopIndex (B : StoppingStrategy m N)
    (ys : List ℝ) {t : ℕ} (ht : t < B.firstStopIndex ys) :
    B.stop ((completeTranscript N ys).take t) ≠ true := by
  intro hstop
  exact Nat.find_min (B.exists_stopped_prefix ys) ht
    ⟨le_trans (Nat.le_of_lt ht) (B.firstStopIndex_le ys), hstop⟩

/-- The genuine transcript on which `B` stops, extracted from any transcript
by first completing it to the fixed horizon. -/
def terminalPrefix (B : StoppingStrategy m N) (ys : List ℝ) : List ℝ :=
  (completeTranscript N ys).take (B.firstStopIndex ys)

@[simp]
theorem length_terminalPrefix (B : StoppingStrategy m N) (ys : List ℝ) :
    (B.terminalPrefix ys).length = B.firstStopIndex ys := by
  rw [terminalPrefix, List.length_take, length_completeTranscript]
  exact Nat.min_eq_left (B.firstStopIndex_le ys)

@[simp]
theorem stop_terminalPrefix (B : StoppingStrategy m N) (ys : List ℝ) :
    B.stop (B.terminalPrefix ys) = true := by
  exact B.stop_firstStopIndex ys

theorem terminalPrefix_isTerminal (B : StoppingStrategy m N) (ys : List ℝ) :
    B.IsTerminalTranscript (B.terminalPrefix ys) := by
  refine ⟨?_, B.stop_terminalPrefix ys, ?_⟩
  · simpa using B.firstStopIndex_le ys
  · intro t ht
    have ht' : t < B.firstStopIndex ys := by simpa using ht
    have htake : (B.terminalPrefix ys).take t =
        (completeTranscript N ys).take t := by
      rw [terminalPrefix, List.take_take, Nat.min_eq_left (Nat.le_of_lt ht')]
    rw [htake]
    exact B.not_stop_before_firstStopIndex ys ht'

theorem terminalPrefix_eq_take {ys : List ℝ} (B : StoppingStrategy m N)
    (hys : ys.length = N) :
    B.terminalPrefix ys = ys.take (B.firstStopIndex ys) := by
  rw [terminalPrefix, completeTranscript_eq_self hys]

/-! ## Padding into the fixed-horizon model -/

/-- Pad a stopping strategy to an ordinary fixed-horizon strategy.  Its
queries after the first stopped prefix are harmless fictitious queries; its
output ignores every answer after that prefix. -/
def pad (B : StoppingStrategy m N) : DeterministicStrategy m where
  query := B.query
  output := fun ys ↦ B.output (B.terminalPrefix ys)

@[simp]
theorem pad_query (B : StoppingStrategy m N) (ys : List ℝ) :
    B.pad.query ys = B.query ys := rfl

@[simp]
theorem pad_output (B : StoppingStrategy m N) (ys : List ℝ) :
    B.pad.output ys = B.output (B.terminalPrefix ys) := rfl

/-- Padding changes only the output rule, so exact consistency is unchanged. -/
theorem consistent_pad_iff_underlying [NeZero m]
    (B : StoppingStrategy m N) (ys : List ℝ) (W : RowMatrix m) :
    Consistent B.pad ys W ↔ Consistent B.underlying ys W := by
  rfl

/-- A full padded transcript restricts to a genuine, exactly consistent
terminal transcript of the stopping algorithm. -/
theorem consistent_terminalPrefix [NeZero m]
    (B : StoppingStrategy m N) {ys : List ℝ} {W : RowMatrix m}
    (hys : ys.length = N) (hconsistent : Consistent B.pad ys W) :
    Consistent B.underlying (B.terminalPrefix ys) W := by
  have htake : Consistent B.pad (ys.take (B.firstStopIndex ys)) W :=
    hconsistent.take (B.firstStopIndex ys)
  rw [B.terminalPrefix_eq_take hys]
  exact (B.consistent_pad_iff_underlying _ _).mp htake

/-- On every full transcript, the padded output is literally the stopping
algorithm's output on its first terminal prefix. -/
theorem pad_output_eq_terminal_output (B : StoppingStrategy m N)
    (ys : List ℝ) :
    (B.pad.output ys : QuerySpace m) =
      (B.output (B.terminalPrefix ys) : QuerySpace m) := rfl

/-! ## Uniform success and the fixed-horizon normal form -/

/-- A particular stopping strategy succeeds to accuracy `ε` on the hard
row-matrix family if it succeeds on every admissible instance and every
exactly consistent terminal transcript. -/
def SucceedsWithin (B : StoppingStrategy m N) [NeZero m] (ε : ℝ) : Prop :=
  ∀ (ys : List ℝ) (W : RowMatrix m),
    B.IsTerminalTranscript ys →
    Admissible W →
    Consistent B.underlying ys W →
    hardObjective W (B.output ys : QuerySpace m) -
        hardObjective W (hardOptimizer W) ≤ ε

/-- Existence of a deterministic strategy making at most `N` exact-value
queries and succeeding uniformly to accuracy `ε`. -/
def AtMostSucceedsWithin (m N : ℕ) [NeZero m] (ε : ℝ) : Prop :=
  ∃ B : StoppingStrategy m N, B.SucceedsWithin ε

/-- The corresponding existential fixed-horizon success predicate. -/
def FixedHorizonSucceedsWithin (m N : ℕ) [NeZero m] (ε : ℝ) : Prop :=
  ∃ A : DeterministicStrategy m,
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = N →
      Admissible W →
      Consistent A ys W →
      hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) ≤ ε

/-- The padding construction preserves every uniform success guarantee. -/
theorem pad_preserves_success [NeZero m] {B : StoppingStrategy m N} {ε : ℝ}
    (hB : B.SucceedsWithin ε) :
    ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = N →
      Admissible W →
      Consistent B.pad ys W →
      hardObjective W (B.pad.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) ≤ ε := by
  intro ys W hys hW hconsistent
  exact hB (B.terminalPrefix ys) W (B.terminalPrefix_isTerminal ys) hW
    (B.consistent_terminalPrefix hys hconsistent)

/-- Every successful at-most-`N` strategy has a successful fixed-horizon
padding. -/
theorem fixedHorizonSucceedsWithin_of_atMostSucceedsWithin [NeZero m] {ε : ℝ}
    (h : AtMostSucceedsWithin m N ε) :
    FixedHorizonSucceedsWithin m N ε := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B.pad, B.pad_preserves_success hB⟩

/-! ## The converse embedding and exact equivalence -/

/-- Regard a fixed-horizon strategy as a stopping strategy which stops exactly
when the transcript has length `N`. -/
def ofFixedHorizon (A : DeterministicStrategy m) (N : ℕ) :
    StoppingStrategy m N where
  query := A.query
  output := A.output
  stop := fun ys ↦ decide (ys.length = N)
  stop_at_bound := by
    intro ys hys
    simp [hys]

@[simp]
theorem ofFixedHorizon_underlying (A : DeterministicStrategy m) (N : ℕ) :
    (ofFixedHorizon A N).underlying = A := rfl

theorem ofFixedHorizon_terminal_length (A : DeterministicStrategy m)
    {ys : List ℝ}
    (hterminal : (ofFixedHorizon A N).IsTerminalTranscript ys) :
    ys.length = N := by
  exact of_decide_eq_true hterminal.2.1

/-- A fixed-horizon success guarantee remains valid when the same strategy is
viewed as stopping exactly at the horizon. -/
theorem ofFixedHorizon_preserves_success [NeZero m]
    {A : DeterministicStrategy m} {ε : ℝ}
    (hA : ∀ (ys : List ℝ) (W : RowMatrix m),
      ys.length = N →
      Admissible W →
      Consistent A ys W →
      hardObjective W (A.output ys : QuerySpace m) -
          hardObjective W (hardOptimizer W) ≤ ε) :
    (ofFixedHorizon A N).SucceedsWithin ε := by
  intro ys W hterminal hW hconsistent
  exact hA ys W (ofFixedHorizon_terminal_length A hterminal) hW hconsistent

theorem atMostSucceedsWithin_of_fixedHorizonSucceedsWithin [NeZero m] {ε : ℝ}
    (h : FixedHorizonSucceedsWithin m N ε) :
    AtMostSucceedsWithin m N ε := by
  obtain ⟨A, hA⟩ := h
  exact ⟨ofFixedHorizon A N, ofFixedHorizon_preserves_success hA⟩

/-- Exact normal-form equivalence between transcript-dependent at-most-`N`
strategies and the repository's fixed-horizon strategies. -/
theorem atMostSucceedsWithin_iff_fixedHorizonSucceedsWithin [NeZero m]
    (ε : ℝ) :
    AtMostSucceedsWithin m N ε ↔ FixedHorizonSucceedsWithin m N ε :=
  ⟨fixedHorizonSucceedsWithin_of_atMostSucceedsWithin,
    atMostSucceedsWithin_of_fixedHorizonSucceedsWithin⟩

/-- Consequently, any fixed-horizon impossibility theorem immediately rules
out algorithms which stop transcript-dependently after at most `N` queries. -/
theorem not_atMostSucceedsWithin_of_not_fixedHorizonSucceedsWithin [NeZero m]
    {ε : ℝ} (h : ¬FixedHorizonSucceedsWithin m N ε) :
    ¬AtMostSucceedsWithin m N ε := by
  exact fun hstop ↦ h (fixedHorizonSucceedsWithin_of_atMostSucceedsWithin hstop)

/-! ## Specialization to the improved `d⁻¹ᵗ²` accuracy -/

/-- The public `SucceedsWithinSqrt` predicate is definitionally the generic
fixed-horizon predicate at `sqrtAccuracy m`. -/
theorem succeedsWithinSqrt_iff_fixedHorizon [NeZero m] :
    SucceedsWithinSqrt m N ↔
      FixedHorizonSucceedsWithin m N (sqrtAccuracy m) := by
  rfl

theorem succeedsWithinSqrt_of_atMost [NeZero m]
    (h : AtMostSucceedsWithin m N (sqrtAccuracy m)) :
    SucceedsWithinSqrt m N := by
  rw [succeedsWithinSqrt_iff_fixedHorizon]
  exact fixedHorizonSucceedsWithin_of_atMostSucceedsWithin h

/-- This is the final padding interface needed by the improved lower bound:
negating fixed-horizon success also negates success by every deterministic
algorithm which stops after at most `N` exact-value queries. -/
theorem not_atMostSucceedsWithinSqrt_of_not_succeedsWithinSqrt [NeZero m]
    (h : ¬SucceedsWithinSqrt m N) :
    ¬AtMostSucceedsWithin m N (sqrtAccuracy m) := by
  exact fun hstop ↦ h (succeedsWithinSqrt_of_atMost hstop)

#print axioms StoppingStrategy.terminalPrefix_isTerminal
#print axioms StoppingStrategy.pad_preserves_success
#print axioms StoppingStrategy.atMostSucceedsWithin_iff_fixedHorizonSucceedsWithin
#print axioms StoppingStrategy.not_atMostSucceedsWithinSqrt_of_not_succeedsWithinSqrt

end StoppingStrategy

end ZeroOrderBounds.AccuracyImprovement
