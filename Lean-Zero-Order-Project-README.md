# Historical project note for the preserved `d⁻³` formalization

> [!NOTE]
> This document records the original `d⁻³`-only project design and is retained
> as documentation for [`ZeroOrderBounds/`](ZeroOrderBounds/).  Its statements
> below about repository-wide Lean scope are historical: the separate
> [`FullDMinusOneHalfAccuracy/`](FullDMinusOneHalfAccuracy/) development now
> fully verifies the paper's deterministic `d⁻¹ᐟ²` lower-bound result.  See
> the current [`README.md`](README.md) for the two-track repository overview.

This repository is the Lean 4 companion to the manuscript
[*Closing the Oracle-Complexity Gap in Derivative-Free Optimization: A Near-Quadratic Lower Bound from Exact Function Values*](zero_order_LB_tex/value_oracle_restructured_submission/value_oracle_accuracy.tex).
The paper and the formal development study deterministic minimization of
convex Lipschitz functions over a Euclidean ball when an oracle returns only
exact function values.

The manuscript proves the sharper accuracy result. In the normalization

- domain: the Euclidean unit ball in dimension \(d\);
- objectives: convex and \(1\)-Lipschitz; and
- oracle: deterministic, sequential, exact-value only,

its lower bound is

\[
Q_{\mathrm{val}}^{\det}\!\left(d,\frac{\varepsilon_0}{\sqrt d}\right)
  = \Omega\!\left(\frac{d^2}{\log(d+1)}\right)
\]

for a universal \(\varepsilon_0>0\). Together with the value-oracle upper
bound discussed in the paper, this gives \(\widetilde\Theta(d^2)\) query
complexity at accuracy \(\Theta(d^{-1/2})\).

The Lean development verifies a complementary, deliberately more
formalization-friendly version of the lower bound. It obtains a genuinely
quadratic query bound at the smaller accuracy scale \(\Theta(d^{-3})\), in
even dimension:

| | Manuscript theorem | Lean-verified theorem |
|---|---|---|
| Accuracy | \(\varepsilon_0 d^{-1/2}\) | \(d^{-3}/25{,}000{,}000\) |
| Lower bound | \(\Omega(d^2/\log d)\) | \(\Omega(d^2)\) |
| Dimensions | all sufficiently large \(d\), using an odd-dimensional embedding | even \(d\ge 2000\) |
| Final separation mechanism | aggregate uncertainty from linearly many rows | uncertainty in one selected row |
| Formal status in this repository | not formalized at the \(d^{-1/2}\) scale | fully kernel-checked |

Thus the formal theorem certifies the central quadratic exact-value lower-bound
mechanism, but it is not a line-by-line formalization of the manuscript's
sharper \(d^{-1/2}\)-accuracy theorem. A lower bound at \(d^{-3}\) accuracy
does not by itself imply a lower bound at the coarser \(d^{-1/2}\) accuracy,
so the two statements should not be conflated.

## The verified theorem

The formal statement uses \(d=2m\). For every \(m\ge 1000\), every horizon
\(T\) satisfying

\[
1000T\le m^2,
\]

and every deterministic exact-value strategy, the resisting oracle constructs
an exact transcript of length \(T\) and an admissible matrix \(W\) such that

\[
f_W(x,z)=\max_{i\in[m]}
  \left\{\frac12 x_i+\langle w_i,z\rangle\right\}
\]

reproduces the complete transcript and the strategy's output \(\widehat q\)
satisfies

\[
f_W(\widehat q)-\min_{q\in B_{2m}} f_W(q)
  > \frac{1}{200{,}000{,}000\,m^3}.
\]

Since \(d=2m\), the hypotheses and gap become

\[
T\le \frac{d^2}{4000},
\qquad
f_W(\widehat q)-\min_{B_d}f_W
  > \frac{1}{25{,}000{,}000\,d^3}.
\]

The public Lean declarations are:

- `ZeroOrderBounds.fixedHorizonLowerBound_strict`, the strict error bound;
- `ZeroOrderBounds.fixedHorizonLowerBound`, its non-strict form; and
- `ZeroOrderBounds.not_succeedsWithin_advertised`, the fixed-horizon
  no-strategy corollary.

The formal `SucceedsWithin` predicate uses a transcript of exactly length
(T). The standard passage from a strategy stopping in at most (T) rounds
uses padding by ignored repeated queries; that variable-stopping-time wrapper
is not separately defined in Lean. Likewise, the conversion from the hard
subclass to the full convex Lipschitz class and the odd-dimensional embedding
are mathematical corollaries rather than additional public declarations.

The strategy model permits arbitrary, potentially discontinuous functions of
the preceding exact real answers and places no computational restriction on
the algorithm. Queries and the final output lie in the Euclidean unit ball.
For every admissible \(W\), the development also proves that \(f_W\) is convex
on the whole ambient space, globally \(1\)-Lipschitz, and zero at the origin,
and it certifies the optimizer used in the final gap statement.

## Why the formal theorem currently has a \(d^{-3}\) gap

Both proofs maintain a Cartesian product of compact convex row bodies whose
members all reproduce the same exact transcript. The formal proof then finds
one row body with enough surviving intrinsic volume, chooses two well-separated
points in that body, and changes only that row. The one-row sensitivity theorem
turns this displacement into separated minimizers. This route isolates the
manuscript-specific analytic argument while keeping the final geometric
selection local to a single uncertainty body; its explicit estimates yield the
verified \(d^{-3}\) objective gap.

At the \(d^{-1/2}\) scale, a single row's displacement is diluted by its
approximately \(1/m\) barycentric weight. The manuscript overcomes that
dilution by retaining large uncertainty in linearly many rows and coordinating
their perturbations. In particular, its sharper argument uses machinery not
present in this Lean development:

- volume-radius-to-mean-width conversion through Urysohn's inequality in the
  affine span of each row body;
- random spherical directions and their projections into many changing affine
  subspaces;
- averaging of widths to obtain one ambient direction with large aggregate
  width; and
- simultaneous perturbation of many rows, together with control of the
  resulting barycentric weights and normalized minimizers.

The repository's current formal scope is therefore the complete one-row
architecture and its explicit \(d^{-3}\) theorem. The paper contains the
additional aggregate-width argument responsible for its stronger
\(d^{-1/2}\)-accuracy result.

## Proof architecture

The proof is organized as a dependency chain of small, independently checked
modules.

1. **Hard family and minimizer geometry.**
   [`Basic.lean`](ZeroOrderBounds/Basic.lean) defines the \(2m\)-dimensional
   block space and numerical parameters.
   [`HardFamily.lean`](ZeroOrderBounds/HardFamily.lean) defines admissible row
   matrices and max-affine objectives and proves convexity and Lipschitzness.
   [`Covariance.lean`](ZeroOrderBounds/Covariance.lean),
   [`ProjectionGeometry.lean`](ZeroOrderBounds/ProjectionGeometry.lean), and
   [`Barycentric.lean`](ZeroOrderBounds/Barycentric.lean) identify the
   minimum-norm slope combination, derive its covariance equation, and certify
   the unit-ball optimizer.

2. **One-row analytic estimate.**
   [`OneRowSensitivity.lean`](ZeroOrderBounds/OneRowSensitivity.lean) proves
   that a controlled change in one row separates the corresponding optimizers.
   The normalization estimate uses the fixed sum of the first-block
   coordinates, avoiding a separate Jacobian analysis.

3. **Intrinsic volume and exact sections.**
   [`IntrinsicVolume.lean`](ZeroOrderBounds/IntrinsicVolume.lean) develops
   intrinsic volume in changing affine hulls.
   [`BallVolumeRatio.lean`](ZeroOrderBounds/BallVolumeRatio.lean) supplies the
   Euclidean ball-volume estimates.
   [`AtomlessQuantile.lean`](ZeroOrderBounds/AtomlessQuantile.lean) proves exact
   quantiles for atomless finite measures, and
   [`QuantileSection.lean`](ZeroOrderBounds/QuantileSection.lean) converts them
   into large affine caps and codimension-one sections.

4. **Exact resisting oracle.**
   [`OracleState.lean`](ZeroOrderBounds/OracleState.lean) defines arbitrary
   deterministic strategies, transcripts, row bodies, and the exact Cartesian
   product consistency invariant.
   [`OracleStep.lean`](ZeroOrderBounds/OracleStep.lean) constructs informative
   section steps and noninformative cap steps while certifying containment,
   dimension change, exact answers, and retained volume.
   [`RepeatedQuery.lean`](ZeroOrderBounds/RepeatedQuery.lean) checks the
   repeated-query edge case.

5. **Iteration and potential.**
   [`VolumePotential.lean`](ZeroOrderBounds/VolumePotential.lean) proves the
   normalized product-volume and entropy estimates.
   [`OracleRun.lean`](ZeroOrderBounds/OracleRun.lean) iterates the oracle for
   exactly \(T\) rounds, counts cuts row by row, and exports the final dimension
   and entropy budgets.

6. **Indistinguishability and final gap.**
   [`GoodRow.lean`](ZeroOrderBounds/GoodRow.lean) extracts a row with a large
   surviving radius.
   [`FinalGap.lean`](ZeroOrderBounds/FinalGap.lean) converts optimizer separation
   into the explicit objective-error constant.
   [`Indistinguishability.lean`](ZeroOrderBounds/Indistinguishability.lean)
   constructs two transcript-compatible row selections that differ only in the
   good row.
   [`Main.lean`](ZeroOrderBounds/Main.lean) assembles the fixed-horizon theorem
   and the no-strategy corollary.

[`ZeroOrderBounds.lean`](ZeroOrderBounds.lean) is the public library root. It
imports the completed theorem and the repeated-query check, so building the
default target checks the complete proof chain.

## Verification status

The formalization is complete for the stated \(d^{-3}\), even-dimensional
theorem. A clean verification run used

```sh
lake clean
lake build
rg -n '\b(sorry|admit|axiom)\b' ZeroOrderBounds ZeroOrderBounds.lean -g '*.lean'
```

The clean build passed after checking 3,491 jobs, and the source scan returned
no matches. There are no `sorry`, `admit`, custom axioms, or placeholder
declarations in the proof. The final `#print axioms` commands report only

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/classical dependencies. Classical choice is expected
because the exact quantiles, affine sections, and resisting-oracle choices are
noncomputable. The development is checked with Lean 4.32.0 and mathlib release
`v4.32.0`, with the exact dependency revisions recorded in
[`lake-manifest.json`](lake-manifest.json).

The detailed build and theorem audit is recorded in the
[`Lean Proof Map`](LEAN_PROOF_MAP.md). The original formalization specification
and proof decomposition are retained in
[`LEAN_FORMALIZATION_INSTRUCTIONS.md`](LEAN_FORMALIZATION_INSTRUCTIONS.md) as a
design record for the completed implementation. The manuscript source is under
[`zero_order_LB_tex/value_oracle_restructured_submission/`](zero_order_LB_tex/value_oracle_restructured_submission/).

This repository formalizes the lower-bound argument only. The upper bound
quoted in the manuscript is not part of the Lean development.
