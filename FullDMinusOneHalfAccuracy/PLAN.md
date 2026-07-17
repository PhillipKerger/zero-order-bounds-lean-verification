# Formalization plan for the `d⁻¹ᐟ²` accuracy lower bound

## 1. Objective and trust boundary

This directory contains the new Lean branch that formalizes the
aggregate-width endgame in `value_oracle_accuracy.tex`.  The target is the
paper's deterministic exact-value lower bound at accuracy of order
`d⁻¹ᐟ²`, not a restatement of the existing `d⁻³` result.

The production endpoint is proved without `sorry`, `admit`, a
project-specific axiom, or an unproved theorem supplied as a typeclass
hypothesis.  Its axiom audit contains only the classical Lean/Mathlib
dependencies already used by the repository (`propext`,
`Classical.choice`, and `Quot.sound`).

The existing `ZeroOrderBounds/` files remain the independently buildable
formalization of the `d⁻³` result.  New code imports and reuses those files;
it does not edit them unless a genuinely general reusable lemma cannot be
proved cleanly in this directory.

## 2. Mathematical target

Write `d = 2m`, use the existing constants

* `a = 1/2`,
* `Gamma = 100`, and
* `tau m = a / (Gamma * sqrt m)`.

For rows `W : Fin m → RowSpace m`, the existing hard objective is

```text
hardObjective W (x,z) = max_i (a * x_i + inner (W i) z).
```

The core fixed-horizon endpoint says, with explicit universal
constants, that whenever

```text
T ≤ (1/100) * m^2 / log (e*m),
```

every deterministic exact-value strategy has a length-`T` transcript and
an admissible, transcript-consistent hard instance on which its final output
has strict objective error larger than `10⁻⁷ / sqrt (2m)` (or a slightly
stronger explicit rational expression from which this inequality follows).

The audit-facing proposition must also expose:

* exact transcript length;
* admissibility of every row;
* `f(0)=0`;
* convexity and global one-Lipschitzness;
* consistency with every exact answer;
* membership and minimality of the certified optimizer; and
* the strict `d⁻¹ᐟ²` objective gap.

The kernel-facing core result is fixed-horizon and even-dimensional, matching
the repository's existing strategy vocabulary and the load-bearing geometric
part of the paper.  The paper-facing development also contains the following
explicit wrappers rather than silently inferring them from the core statement:

1. a no-fixed-horizon-strategy theorem at the same strict accuracy;
2. a proved padding/serialization reduction from algorithms making at most
   `T` transcript-dependent queries to the fixed-horizon model;
3. the floor choice
   `N_m = floor ((1/100) * m^2 / log (e*m))` and a query-complexity theorem
   giving `Omega(d^2 / log(d+1))`;
4. the odd-dimensional embedding from `d - 1` to `d`; and
5. scaling from the unit ball and unit Lipschitz constant to radius `R` and
   Lipschitz constant `L`, together with monotonicity in the target error.

The Protasov upper bound, the two-sided `widetildeTheta` conclusion, and the
mixed-integer transfer are separate mathematical results in the paper.  They
are ancillary to this directory's lower-bound target and must not be claimed
as formally verified unless separately implemented.

## 3. Reused formalization

The following existing modules are the trusted shared backbone.

| Paper component | Existing Lean source | Reused declarations |
|---|---|---|
| Euclidean block model and constants | `ZeroOrderBounds/Basic.lean` | `RowSpace`, `QuerySpace`, `unitBall`, `a`, `Gamma`, `tau` |
| Hard max-affine family | `ZeroOrderBounds/HardFamily.lean` | `RowMatrix`, `Admissible`, `hardObjective`, class certificates |
| Projection/minimizer geometry | `ZeroOrderBounds/ProjectionGeometry.lean` | `minWeights`, `minPoint`, `hardOptimizer`, growth and norm bounds |
| Barycentric stationarity | `ZeroOrderBounds/Barycentric.lean` | `zBlock`, `minWeights_apply_eq`, `norm_zBlock_le_tau` |
| Intrinsic affine volume | `ZeroOrderBounds/IntrinsicVolume.lean` | `affineDim`, `intrinsicVolumeReal`, `IntrinsicBody` |
| Row uncertainty bodies | `ZeroOrderBounds/OracleState.lean` | `RowBody`, `rowProduct`, `ProductConsistent`, `OracleState` |
| Exact resisting oracle | `OracleStep`, `OracleRun` | final row bodies and exact product invariant |
| Normalized-volume potential | `VolumePotential`, `GoodRow` | `normalizedVolume`, `rowEntropy`, `entropyScale`, final budgets |
| Final objective growth | `FinalGap` | `one_of_two_objective_gaps`, `hardObjective_growth_uniform` |

In particular, `oracleRun_final_budgets` already supplies for the final row
bodies `P_i`:

```text
dim P_i = m - c_i,
sum_i c_i ≤ T,
sum_i (-log rho_i) ≤ T * entropyScale m,
```

where `rho_i` is the normalized intrinsic volume.  No second oracle or
volume-potential implementation should be introduced.

## 4. Implemented module graph and status

The implementation is more granular than the paper.  Every node below is a
checked Lean module; arrows point from prerequisites to consumers.

```text
Existing exact oracle and potential (`ZeroOrderBounds/`)
  Basic + HardFamily + ProjectionGeometry + Barycentric
  QuantileSection + OracleState + OracleStep + OracleRun + VolumePotential
          |                                      |
          |                                      +--> Numerics
          |                                             |
          |                                             +--> ManyGoodRows
          |
          +--> BarycentricStability --> AggregateSeparation
                    ^                       ^
                    |                       |
             SimultaneousSelections --------+

Spherical width and projection
  DirectionalWidth --> SphereMeasure --> PolarFactorization
          |                                      |
          |                                      +--> SphericalProjection
          |                                                  |
          +--------------------------------------------------+
                                                             |
                                    CommonDirection <---------+
                                    RowProjectionBridge <-----+

Brunn--Minkowski and Urysohn
  BorellBrascampLiebAlgebra
          |
  BrunnMinkowski (definitions, homothetic cases, dimension-one base)
          |
          +--> BrunnMinkowskiSlices --> BrunnMinkowskiSliceProfiles
          |                                  |             |
          |                                  |             +--> SliceProjectionPositive
          |                                  +------------------> SliceProfilePositivity
          |
  ConcaveDensityTransport --> BBLIntegrableTransport
          |
  BrunnMinkowskiReduction (equal-volume and zero-volume reductions)
          |
  BrunnMinkowskiTransport --> BrunnMinkowskiProduct
                                      |
                                      +--> BrunnMinkowskiInduction
                                           (all positive Euclidean dimensions)

Haar/Minkowski assembly of Urysohn
  MinkowskiWidth + OrthogonalHaar + SupportFunction + RotationAction
          |                       |
          |                       +--> HaarSupportAverage
          +--> FiniteBrunnMinkowski ---------+
  ConvexVolumeLimit -------------------------+
  IntrinsicCoordinates ----------------------+
                                              |
                                              +--> UrysohnAssembly
                                                        |
                                                        +--> RowUrysohnConsequence
                                                                   |
                                    BrunnMinkowskiInduction --------+--> UrysohnMain

Optimization endgame
  CommonDirection + AggregateSeparation --> WidthEndgame --> FinalAssembly
  ManyGoodRows + RowProjectionBridge + FinalAssembly
                                      |
                                      +--> ConditionalMain --> MainBridge
                                                                   ^
                                      BrunnMinkowskiInduction ------+
                                                                   |
             Statement --> Challenge-full-d-1-2-accuracy           +--> Main
                                      Main --> Solution --> Audit       |
                                                                   +---+---+
                                                                   |       |
                                           StoppingStrategy + QueryBudget  |
                                                        |                  |
                                                        +--> ComplexityBridge
                                                                   |
                                                                   +--> Main

Dimension and scale transports
  OddDimension + Main --> OddMain
  Scaling      + Main --> ScaledMain
  OddMain + ScaledMain --> PaperStopping
                              (odd and scaled at-most-query endpoints)
```

`BBLSmoothTransport.lean` is a checked alternate smooth transport route; the
endpoint-robust production route is `BBLIntegrableTransport.lean`.
`BrunnMinkowskiProduct.lean` proves the induction step on
`WithLp 2 (ℝ × V)`, including positive-volume normalization and both
degenerate-volume cases.  `BrunnMinkowskiTransport.lean` supplies the
measure-preserving coordinate transports, and
`BrunnMinkowskiInduction.lean` closes the induction in every positive standard
Euclidean dimension.

`Main.lean` is unconditional: it instantiates `MainBridge` with
`euclidean_brunnMinkowski_family`.
`Challenge-full-d-1-2-accuracy.lean` contains the one intentional
statement-fixture `sorry`; production `Solution.lean` delegates to `Main`, and
`Audit.lean` guards the permitted axiom set.  The Comparator
configuration is
`FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json`.

### 4.1 Completed core

The following layers are present and build together:

* the paper logarithm and all final numerical constants;
* the many-good-rows argument from the existing exact oracle budgets;
* directional width, normalized sphere measure, spherical projection, and
  the common-direction averaging theorem;
* sharp barycentric stability, simultaneous extremal selections, aggregate
  optimizer separation, indistinguishability, and the final growth estimate;
* the Haar approximation, finite rotated Minkowski sums, volume limiting,
  intrinsic-coordinate transport, and Urysohn assembly conditional only on
  Brunn--Minkowski;
* the one-dimensional, slice-profile, endpoint-robust BBL, product-space, and
  dimension-induction proof of finite-dimensional Brunn--Minkowski;
* intrinsic Urysohn and its row-normalized consequence, discharged from that
  unconditional Brunn--Minkowski theorem in `UrysohnMain.lean`; and
* the unconditional fixed-horizon theorem, solution wrapper, and guarded
  axiom audit.

In particular, `ConditionalMain.lean` proves
`fixedHorizonLowerBound_strict_of_intrinsic_urysohn`, the complete
optimization theorem from the exact row-level Urysohn consequence.
`Main.lean` discharges that premise and exports
`fixedHorizonSqrtLowerBound_strict` with the exact Comparator statement.

### 4.2 Completed lower-bound wrappers

The following paper-facing reductions are also checked:

* `StoppingStrategy.lean` models transcript-dependent stopping, proves the
  padding simulation, and identifies at-most and fixed-horizon success;
* `QueryBudget.lean` defines the floored horizon and proves the explicit even
  rate `d² / (800 log(d+1))` below the first horizon not ruled out;
* `ComplexityBridge.lean` and `Main.lean` expose unconditional fixed-horizon,
  at-most-budget, and integer-rate impossibility statements;
* `OddDimension.lean` proves the projection/lift transport to dimension
  `2m+1`, and `OddMain.lean` exports its unconditional fixed-horizon endpoint
  at accuracy `10⁻⁷ / sqrt(2m+1)`, its floored-budget impossibility theorem,
  and the explicit odd rate with denominator constant `1800`; and
* `Scaling.lean` transports queries, exact transcripts, objectives, and
  optimizers between the unit model and a radius-`R`, `L`-Lipschitz model.
  `ScaledMain.lean` exports the unconditional scaled fixed-horizon theorem and
  its monotone smaller-error form;
* `PaperStopping.lean` factors terminal-prefix bookkeeping into a generic
  exact-real stopping rule, proves padding equivalences for the ambient and
  radius-scaled strategy types, and exports odd-dimensional and scaled
  at-most-budget impossibility theorems.  The scaled form covers every
  `ε ≤ (L*R) * sqrtAccuracy m`.

### 4.3 Honest remaining scope

The checked wrappers are separate public declarations rather than one final
theorem simultaneously quantifying over arbitrary `d`, radius, Lipschitz
constant, and target accuracy.  Even and odd dimensions have explicit
floor/rate and at-most-query endpoints; the scaled at-most endpoint currently
uses the even block model.  A single odd-plus-scaled all-parameter convenience
theorem would be packaging, not a missing geometric argument.

The Protasov upper bound, polynomial-accuracy upper corollary, two-sided
`widetildeTheta` conclusion, common-optimum binning/flooring transform, radial
box extension, and mixed-integer transfer remain unformalized.

## 5. Detailed lemma plan

### 5.1 `Numerics.lean` — implemented

This file collects the general logarithm, cast, root, and fixed-constant
estimates used by later modules.  Its implemented statements include:

* positivity and monotonicity facts for `log (exp 1 * m)`;
* `entropyScale m ≤ 4 * log (exp 1 * m)` for positive `m` (the paper's
  entropy budget, allowing the existing slightly looser scale if needed);
* conversions between the natural query condition and real inequalities;
* the `eta = 1/100`, `Gamma = 100` rational inequalities;
* `sqrt (1 + Gamma⁻²) ≤ 1 + 1/(2 Gamma²)`;
* the final comparisons with `1/600`, `1/1200`, and
  `10⁻⁷ / sqrt (2m)`.

The geometric files should end in symbolic bounds; fixed arithmetic belongs
here so that reviewers can audit constants independently.

### 5.2 `ManyGoodRows.lean` — implemented

This file defines a row to be good when both

```text
c_i ≤ 4 * eta * m
rowEntropy rho_i ≤ 16 * eta * m.
```

Because natural codimensions do not literally support the first real-valued
display, the Lean predicate uses cast inequalities.  The file proves:

1. Markov/cardinality lemma for a finite family of nonnegative real values.
2. At most `m/4` rows have excessive codimension.
3. At most `m/4` rows have excessive entropy.
4. The complement `G` has cardinality at least `m/2`.
5. For `i ∈ G`, `dim P_i ≥ (1 - 4 eta)m`, hence it is positive.
6. For `i ∈ G`,
   `rho_i ^ ((dim P_i : ℝ)⁻¹) ≥ exp (-1/6) > 1/2`.

The end-to-end theorem `oracleRun_many_good_rows` consumes the three conclusions of
`oracleRun_final_budgets` and the paper horizon condition and returns a
`Finset (Fin m)` of good rows with all dimension/root-volume facts bundled.

### 5.3 `DirectionalWidth.lean` — implemented

For a nonempty compact set `P` in a finite-dimensional real inner-product
space this file defines

```text
directionalWidth P theta =
  sSup ((fun p => inner theta p) '' P) -
  sInf ((fun p => inner theta p) '' P).
```

Compact extrema are chosen by Mathlib compactness results and proved equal to
this canonical value.  The file establishes:

* nonnegativity;
* translation invariance;
* positive homogeneity;
* dependence only on projection to `lin(P-P)`;
* continuity and measurability in `theta`;
* the bound `directionalWidth P theta ≤ 2*r*‖theta‖` when
  `P ⊆ closedBall 0 r`;
* existence of maximizing and minimizing points realizing the width.

### 5.4 `SphereMeasure.lean` — implemented

This file uses Mathlib's `Measure.toSphere volume` rather than inventing a
probability space.  It defines normalized spherical probability measure on
`Metric.sphere (0 : E) 1` by scaling `volume.toSphere` by its finite positive
total mass and proves:

* it is a probability measure in positive dimension;
* invariance under linear isometries (as much as later files require);
* integrability of continuous bounded width functions;
* integral-average existence: a continuous function on the sphere whose
  integral is at least `c` attains a value at least `c`.

The normalization constant should remain abstract whenever it cancels.

### 5.5 Brunn--Minkowski, Haar averaging, and Urysohn — implemented

Mathlib does not currently provide the required Urysohn inequality, so this
development proves it from Brunn--Minkowski and finite Haar averages.

The following supporting files are implemented:

* `BrunnMinkowski.lean` defines the homogeneous volume root and
  `BrunnMinkowskiAt`, proves homothetic cases, and proves the complete
  one-dimensional theorem;
* `BrunnMinkowskiSlices.lean`, `BrunnMinkowskiSliceProfiles.lean`,
  `SliceProjectionPositive.lean`, and `SliceProfilePositivity.lean` formalize
  compact convex slices, Cavalieri, projection intervals, concavity,
  continuity, and strict positivity of slice-radius profiles;
* `BorellBrascampLiebAlgebra.lean`, `ConcaveDensityTransport.lean`, and
  `BBLIntegrableTransport.lean` prove the inverse-CDF algebra and an
  endpoint-robust one-dimensional BBL theorem suitable for those profiles;
* `BrunnMinkowskiReduction.lean` reduces the general positive-volume theorem
  to the equal-volume case and separately closes both zero-volume cases;
* `BrunnMinkowskiTransport.lean` proves volume and weighted-Minkowski
  invariance under measure-preserving continuous linear equivalences;
* `BrunnMinkowskiProduct.lean` proves the full successor step in
  `WithLp 2 (ℝ × V)` from lower-dimensional Brunn--Minkowski; and
* `BrunnMinkowskiInduction.lean` supplies the one-dimensional coordinate
  transport, the successor Euclidean splitting, and the unconditional theorem
  `brunnMinkowskiAt_euclidean` in every positive dimension;
* `MinkowskiWidth.lean`, `OrthogonalHaar.lean`, `SupportFunction.lean`,
  `RotationAction.lean`, `ConvexVolumeLimit.lean`,
  `FiniteBrunnMinkowski.lean`, and `HaarSupportAverage.lean` construct finite
  averages of rotated difference bodies and pass their support bounds to a
  mean-width ball; and
* `IntrinsicCoordinates.lean` transports an arbitrary affine-hull body to a
  full-dimensional convex body in its direction space while preserving
  intrinsic volume and mean width.

`UrysohnAssembly.lean` proves, from a midpoint Brunn--Minkowski premise,
the full-width inequality

```text
2 * (volume P / volume unitBall)^(1/k)
  ≤ integral_{unit sphere} directionalWidth P
```

and transports it to arbitrary affine hulls.  The row normalization algebra
is completed in `RowUrysohnConsequence.lean`, whose endpoint says that
normalized volume radius greater than `1/2` implies intrinsic mean width at
least `tau m`.  `MainBridge.lean` instantiates every such premise with
`euclidean_brunnMinkowski_family`; no geometric theorem hypothesis reaches the
production endpoint.  `UrysohnMain.lean` also exports the sharp intrinsic and
row-level consequences as standalone unconditional declarations.

### 5.6 `PolarFactorization.lean` and `SphericalProjection.lean` — implemented

For a subspace `L` of ambient Euclidean space, these files formalize the
projection-averaging identity needed by the paper without relying on informal
random-variable notation.

Implemented results include:

* width ignores `Lᗮ` and is homogeneous in the projected vector;
* under ambient normalized sphere measure,
  `integral ‖proj_L theta‖² = finrank L / finrank E`;
* because `0 ≤ R ≤ 1`,
  `integral R ≥ integral R²`;
* the angular part of the projected direction has normalized spherical law
  on `L`, and the radial and angular integrals factor for homogeneous
  functions;
* consequently, for nonnegative width,

```text
ambientMeanWidth P
  = (ambient mean projection radius) * intrinsicMeanWidth P.
```

The implementation uses radial Gaussian factorization locally and pushes the
identity to normalized sphere measure; the final public statement is
measure-independent.

### 5.7 `CommonDirection.lean` and `RowProjectionBridge.lean` — implemented

For the good-row finset `G`, these files combine:

1. Urysohn: intrinsic mean width of each good row is at least `tau m`;
2. projection averaging: ambient mean width is at least half of that because
   `dim P_i / m ≥ 1 - 4 eta ≥ 1/2`;
3. linearity of the finite sum integral; and
4. `G.card ≥ m/2`.

Conclude that there exists an ambient unit vector `theta` with

```text
sum i in G, directionalWidth (P_i) theta ≥ m * tau m / 4.
```

`exists_common_direction_of_row_meanWidth` returns `theta`, its unit norm,
and the aggregate inequality in exactly the form consumed by simultaneous
row selection.  `RowProjectionBridge` supplies the preceding intrinsic-to-
ambient factor-two estimate for a `24/25`-dimensional row.

### 5.8 `BarycentricStability.lean` — implemented

This file adds the manuscript's quantitative consequences of the already-
formalized barycentric formula:

* `‖rowMean W‖ ≤ tau m` (reuse);
* `‖zBlock W‖ ≤ tau m` (reuse);
* coordinatewise closeness
  `|minWeights W i - 1/m| ≤ 2/(Gamma²*m)`;
* sharp squared norm bound
  `‖minPoint W‖² ≤ (a²/m) * (1 + Gamma⁻²)`;
* hence
  `a/sqrt m ≤ ‖minPoint W‖ ≤ (a/sqrt m)*sqrt(1+Gamma⁻²)`.

These statements apply to every admissible matrix and are independent of the
oracle.

### 5.9 `SimultaneousSelections.lean` and `AggregateSeparation.lean` — implemented

Given final row bodies, a good-row set, and the common direction, these files:

1. choose `w_i⁺` and `w_i⁻` realizing max/min direction on each good row;
2. choose a common point for every non-good row;
3. assemble `W⁺` and `W⁻` in the same final row product;
4. prove their mean row displacement in direction `theta` is at least
   `tau m / 4`;
5. use weight closeness to prove
   `inner theta (zBlock W⁺ - zBlock W⁻) > tau m / 5`;
6. infer `‖minPoint W⁺ - minPoint W⁻‖ > tau m / 5`;
7. separate angular from radial change using the sharp norm interval; and
8. close the `Gamma = 100` arithmetic to obtain
   `‖hardOptimizer W⁺ - hardOptimizer W⁻‖ > 1/600`.

The simultaneous matrix construction and analytic separation are separate
theorems so that the exact product-membership proof is easy to audit.

### 5.10 `WidthEndgame.lean` and `FinalAssembly.lean` — implemented

These files use `OracleState.every_selection_consistent` for both matrices.
At the common strategy output, `one_of_two_objective_gaps` with separation
`1/600` gives a gap on one matrix.  `Numerics.lean` proves the explicit
comparison

```text
10^(-7) / sqrt (2*m)
  < a/(8*sqrt m) * (1/600)^2.
```

`OracleState.exists_consistent_selection_with_sqrt_gap_of_row_meanWidths`
returns the failing matrix with row-product membership, exact transcript
consistency, and the strict objective gap.  The public-shape theorem
`fixedHorizonLowerBound_strict_of_row_meanWidths` adds the transcript length,
hard-function class certificates, and optimizer certificate.

### 5.11 `ConditionalMain.lean`, `MainBridge.lean`, and `Main.lean` — implemented

The theorem `fixedHorizonLowerBound_strict_of_intrinsic_urysohn` in
`ConditionalMain.lean` already assembles, in order:

1. `oracleStateAt A T` and `oracleRun_final_budgets` through
   `oracleRun_many_good_rows`;
2. at least half the rows with the paper dimension and volume-radius bounds;
3. the row-level intrinsic mean-width consequence supplied as an explicit
   premise;
4. spherical projection and the common-direction theorem;
5. simultaneous opposite row selections and optimizer separation;
6. the one-of-two objective gap; and
7. existing optimizer and objective-class certificates.

`MainBridge.lean` turns the dimension-uniform Euclidean Brunn--Minkowski family
into the complete optimization conclusion.  `Main.lean` applies that bridge
to `euclidean_brunnMinkowski_family` and exposes
`fixedHorizonSqrtLowerBound_strict` with the same statement as the challenge.
No Brunn--Minkowski or Urysohn premise remains in this public endpoint.

### 5.12 Statement, challenge, solution, and audit boundaries — implemented

`Statement.lean` and `Challenge-full-d-1-2-accuracy.lean` are implemented.
`Statement.lean` imports only the definitions required to state the result,
not the proof chain, and defines `sqrtAccuracy` and `SucceedsWithinSqrt`.  The
challenge contains the reviewed theorem and one intentional `sorry`.

`Solution.lean` repeats the challenge statement verbatim and delegates to the
unconditional production endpoint.  The Comparator configuration compares
`fixedHorizonSqrtLowerBound_strict` and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

`Audit.lean` uses guarded `#print axioms` output for the Euclidean
Brunn--Minkowski family, unconditional intrinsic and row-level Urysohn,
production and Comparator endpoints, normalized and odd rate theorems, and
scaled fixed-horizon and transcript-dependent stopping endpoints.

### 5.13 Paper-level lower-bound wrappers — implemented as composable endpoints

The fixed-horizon even-dimensional theorem is the kernel-facing core.  The
following checked modules expose the paper-facing reductions without making
them part of the narrow Comparator statement.

1. **No-strategy wrapper.** `Main.not_succeedsWithinSqrt` contradicts the
   strict witness returned for a purported `SucceedsWithinSqrt` strategy.
2. **At-most/padding wrapper.** `StoppingStrategy.lean` defines a variable-horizon
   algorithm or stopping policy whose stop decision and output may be
   arbitrary functions of the exact real transcript.  Its padded strategy
   retains the stopped output, and the file proves transcript simulation and
   equivalence of at-most and fixed-horizon success.
3. **Floor and query complexity.** `QueryBudget.lean` defines the natural query budget
   corresponding to
   `floor ((1/100) * m^2 / log (e*m))`, proves it satisfies the real horizon,
   and establishes the explicit even-dimensional inequality
   `d² / (800 log(d+1)) < paperQueryBudget m + 1`.  `Main.lean` combines it
   with the at-most impossibility theorem.
4. **Odd dimension.** `OddDimension.lean` implements `F(x,t)=f(x)` and projects
   queries and outputs from `2m+1` dimensions to the even block space.
   `OddMain.lean` preserves ball membership, exact responses, minimizers, and
   the objective gap at ambient accuracy `10⁻⁷ / sqrt(2m+1)`.  It also proves
   floored-budget impossibility and the rate
   `d² / (1800 log(d+1)) < paperQueryBudget m + 1`.
   `PaperStopping.lean` supplies the corresponding transcript-dependent
   at-most-query theorem.
5. **Scaling.** `Scaling.lean` formalizes point and answer scaling, exact
   strategy round trips, class membership, optimizer transport, and gap
   scaling.  `ScaledMain.lean` gives the radius-`R`, `L`-Lipschitz endpoint and
   monotonicity for all smaller requested errors.  `PaperStopping.lean` proves
   the scaled at-most-budget version and pairs it with the explicit even rate.

At-most theorems are packaged for the normalized even and odd models and for
the scaled even model.  There is no single declaration combining odd ambient
dimension with radius/Lipschitz scaling.

The Protasov upper bound, polynomial-accuracy upper corollary, common-optimum
binning/flooring transform, radial box extension, and mixed-integer transfer
are explicitly outside this lower-bound wrapper layer.  They require separate
formalization before the paper's two-sided or mixed-integer claims can be
advertised as verified.

## 6. Verification sequence

The final verification sequence is:

1. `lake build ZeroOrderBounds` checks the preserved `d⁻³` proof;
2. `lake build FullDMinusOneHalfAccuracy` checks the new production root;
3. `lake build 'FullDMinusOneHalfAccuracy.«Challenge-full-d-1-2-accuracy»'
   FullDMinusOneHalfAccuracy.Solution` checks the new Comparator pair;
4. direct `lake env lean --trust=0` checks cover
   `BrunnMinkowskiInduction.lean`, `Main.lean`, `OddMain.lean`,
   `ScaledMain.lean`, `PaperStopping.lean`, and `Audit.lean`;
5. scan production `.lean` files for `sorry`, `admit`, `axiom`,
   `native_decide`, unsafe escape hatches, and unexpected `Classical.choice`
   wrappers around propositions;
6. run Comparator with
   `FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json`; and
7. run the old audit and Comparator configuration independently.

The renamed root challenge/comparator pair continues auditing the `d⁻³`
endpoint independently.

## 7. Documentation and endpoint inventory

The repository-level `README.md`, `VERIFICATION.md`, and
`formalization.yaml` distinguish the preserved `d⁻³` endpoint from the new
`d⁻¹ᐟ²` endpoint.  The narrow audited declaration is the even-dimensional
fixed-horizon theorem in `Main.lean`; at-most, floor/rate, odd-dimensional,
and scaling declarations are listed separately so their quantifier scopes
are not conflated.

## 8. Known risks and how the structure contains them

* **Brunn--Minkowski and Urysohn are absent from current Mathlib.**  Haar
  averaging, intrinsic transport, Urysohn, the product step, and the Euclidean
  dimension induction are isolated from the oracle and implemented here.
* **Variable-dimensional spheres.**  Affine-hull translation and direction
  subtypes are handled before normalization in `IntrinsicCoordinates`; zero
  dimension is excluded by the good-row dimension bound.
* **Sphere normalization constants.**  Work with normalized measures at
  public interfaces; `SphereMeasure` proves total mass positivity once.
* **Projection angular singularity at zero.**  The implementation uses a
  total fallback direction and a radial Gaussian factorization, making the
  zero-projection value harmless.
* **Strict versus weak constants.**  Preserve the paper's slack (`> 1/2`,
  `> tau/5`, `> 1/600`) rather than normalizing all steps to equality.
* **Natural/real coercions in cardinality bounds.**  Keep generic finite-sum
  Markov lemmas separate from paper constants.
* **Exact-`T` versus at-most-`T`.**  A prose padding argument is not a formal
  reduction when stopping depends on arbitrary exact reals.
  `StoppingStrategy.lean` therefore defines the stopping model and proves
  transcript/output preservation in the core block model;
  `PaperStopping.lean` proves the ambient and scaled analogues.
* **Even versus odd dimension.**  `QuerySpace m` builds the `2m` block model
  into its type.  `OddDimension.lean` supplies explicit dimension-generic
  Euclidean embeddings and strategy transport.
* **Accidental circular imports.**  Statement vocabulary and audit wrappers
  are leaves; geometry never imports optimization assembly.
* **Regression of the existing result.**  New declarations live in this
  directory and the existing library is rebuilt at every milestone.

## 9. Completion criteria

### 9.1 Kernel-facing even-dimensional core

The core implementation contains all of the following:

* general finite-dimensional Brunn--Minkowski and hence intrinsic Urysohn are
  unconditional checked Lean declarations;
* the new public fixed-horizon theorem has the paper's `d⁻¹ᐟ²` objective
  scale and `m²/log m` horizon scale;
* the returned hard function is certified convex, one-Lipschitz, normalized,
  exactly transcript-consistent, and equipped with a true minimizer;
* `Main.lean`, `Solution.lean`, and `Audit.lean` exist;
* production code contains no placeholders, theorem premises standing in for
  the target geometry, or project axioms;
* a Comparator challenge/solution configuration for statement comparison;
* guarded `#print axioms` expectations containing only the permitted standard
  dependencies; and
* the old `d⁻³` endpoint still builds and retains its existing audit.

### 9.2 Implemented paper-facing lower-bound components

The core is supplemented by checked theorems for:

* nonexistence of a successful fixed-horizon strategy;
* padding from transcript-dependent at-most-query algorithms;
* the floored query budget and the explicit
  `Omega(d^2 / log(d+1))` complexity inequality;
* the odd-dimensional embedding; and
* radius/Lipschitz scaling and error monotonicity.

These results are composable but are not exported as one theorem combining
odd ambient dimension with radius/Lipschitz scaling.  Documentation should
name the applicable declarations rather than imply that broader combined
type.

### 9.3 Ancillary paper results

The Protasov upper bound, the resulting two-sided `widetildeTheta(d^2)`
statement, the polynomial-accuracy corollary, and the mixed-integer theorem
are not completion requirements for this lower-bound directory.  They remain
unverified paper claims unless separately formalized and audited.
