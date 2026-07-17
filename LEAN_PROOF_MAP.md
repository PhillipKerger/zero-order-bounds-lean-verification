# Lean proof map for the preserved `d⁻³` track

> [!NOTE]
> This is the proof map for the original, simpler `d⁻³` development in
> [`ZeroOrderBounds/`](ZeroOrderBounds/).  It predates the separate
> [`FullDMinusOneHalfAccuracy/`](FullDMinusOneHalfAccuracy/) formalization,
> which now fully verifies the paper's deterministic `d⁻¹ᐟ²` lower bound.
> See the current [`README.md`](README.md) and that folder's
> [`PLAN.md`](FullDMinusOneHalfAccuracy/PLAN.md) for repository-wide scope.

## 1. What is verified

The kernel-checked entry point is
`ZeroOrderBounds.fixedHorizonLowerBound_strict` in
[ZeroOrderBounds/Main.lean](ZeroOrderBounds/Main.lean).

Let the ambient Euclidean dimension be \(d=2m\). For every \(m\ge1000\),
every \(T\) with \(1000T\le m^2\), and every deterministic strategy \(A\),
Lean constructs an exact answer list `ys` of length \(T\) and an admissible
row matrix \(W\) such that:

- \(W\) reproduces every answer at the query determined by the preceding
  exact-real transcript;
- `hardOptimizer W` lies in the unit ball and minimizes `hardObjective W`
  there; and
- the strategy output has strict error

\[
 f_W(A(\mathtt{ys}))-f_W(q_W^*)
 >
 \frac{1}{200{,}000{,}000\,m^3}.
\]

The same file exports the non-strict theorem `fixedHorizonLowerBound` and the
hard-family no-strategy theorem `not_succeedsWithin_advertised`.

For \(d=2m\), the arithmetic translation is

\[
 4000T\le d^2,
 \qquad
 \frac{1}{200{,}000{,}000m^3}
 =
 \frac{1}{25{,}000{,}000d^3}
 =
 4\cdot10^{-8}d^{-3}.
\]

Thus this is an \(\Omega(d^2)\) fixed-horizon lower bound at the explicit
accuracy \(10^{-8}d^{-3}\) in even dimensions, and in particular implies the
requested \(\Omega(d^2/\log(d+1))\) bound at that accuracy.

Scope boundaries:

1. `SucceedsWithin` is an exact length-\(T\) predicate. Padding an algorithm
   that stops in at most \(T\) rounds is a standard mathematical reduction,
   but a variable-stopping strategy type and padding theorem are not packaged
   in Lean.
2. Lean directly checks the even-dimensional hard-family theorem. The
   odd-dimensional embedding and passage from this hard subclass to the full
   convex one-Lipschitz class are mathematical corollaries, not separate
   public declarations.
3. The manuscript's stronger \(d^{-1/2}\)-accuracy theorem is not formalized.

## 2. Dependency overview

~~~text
Euclidean blocks -> hard family -> projection/barycentric geometry
                                      -> covariance -> one-row sensitivity --+
                                                                                |
intrinsic volume -> exact quantiles/sections -> oracle state/step -> iteration  |
                 -> ball-volume ratio ---------> volume potential -> good row --+
                                                                                |
                         indistinguishability + quadratic growth -> Main theorem
~~~

[ZeroOrderBounds.lean](ZeroOrderBounds.lean) imports `Main` and
`RepeatedQuery`, so the default `lake build` reaches the complete proof chain.

## 3. Notation map

| Mathematics | Lean representation | Declaration |
|---|---|---|
| \(E_m=\mathbb R^m\) | Euclidean space indexed by `Fin m` | `RowSpace` in [Basic.lean](ZeroOrderBounds/Basic.lean) |
| \(Q_m=\mathbb R^{2m}\) | Euclidean space indexed by `Fin m ⊕ Fin m` | `QuerySpace` in [Basic.lean](ZeroOrderBounds/Basic.lean) |
| Euclidean unit ball | closed ball in `QuerySpace m` | `unitBall` |
| \(W=(w_i)\) | `Fin m → RowSpace m` | `RowMatrix` in [HardFamily.lean](ZeroOrderBounds/HardFamily.lean) |
| \(\|w_i\|\le\tau\) | predicate on row matrices | `Admissible` |
| \(f_W\) | finite maximum of row forms | `hardObjective` |
| Closest slope combination \(p_W\) | minimum-norm simplex image | `minPoint` in [ProjectionGeometry.lean](ZeroOrderBounds/ProjectionGeometry.lean) |
| \(q_W^*=-p_W/\|p_W\|\) | normalized negative minimum point | `hardOptimizer` |
| Row body \(P_i^t\) | compact convex intrinsic body | `RowBody` in [OracleState.lean](ZeroOrderBounds/OracleState.lean) |
| \(\rho_i=V_i/(\kappa_{k_i}\tau^{k_i})\) | normalized row volume | `RowBody.normalizedVolume` in [VolumePotential.lean](ZeroOrderBounds/VolumePotential.lean) |

## 4. Detailed proof path

### Step 1: Euclidean blocks and the hard family

[Basic.lean](ZeroOrderBounds/Basic.lean) uses one Euclidean space indexed by a
sum type, avoiding the wrong norm on an ordinary product. Audit:

- `joinBlocks_norm_sq`:
  \(\|\operatorname{join}(x,z)\|^2=\|x\|^2+\|z\|^2\);
- `a`, `Gamma`, and `tau`:
  \(a=1/2\), \(\Gamma=100\), and \(\tau=a/(\Gamma\sqrt m)\);
- `abs_coordinateSum_le`:
  \(|S(q)|\le\sqrt m\,\|q\|\).

[HardFamily.lean](ZeroOrderBounds/HardFamily.lean) defines

\[
 v_i=(ae_i,w_i),
 \qquad
 f_W(q)=\max_i\langle v_i,q\rangle.
\]

The declarations `hardObjective_zero`, `convexOn_hardObjective`, and
`hardObjective_lipschitzWith_one` prove normalization, global convexity, and
global one-Lipschitzness for admissible \(W\). The public theorem returns
`Admissible W`; these separate generic lemmas put its witness in the intended
objective class.

### Step 2: Optimizer and quadratic growth

[ProjectionGeometry.lean](ZeroOrderBounds/ProjectionGeometry.lean) maps the
probability simplex into the convex hull of the hard slopes.

1. `exists_minWeights` obtains weights satisfying the projection variational
   inequality, exposed by `minPoint_projection`.
2. `a_div_sqrt_le_norm_minPoint` proves
   \(a/\sqrt m\le\|p_W\|\).
3. `norm_minPoint_le_two_a_div_sqrt` proves
   \(\|p_W\|\le2a/\sqrt m\) for admissible \(W\).
4. `hardOptimizer` defines \(-p_W/\|p_W\|\).
5. `hardOptimizer_mem_unitBall` and `hardOptimizer_isMinOn` certify
   feasibility and optimality.
6. `hardObjective_growth` proves

   \[
   f_W(q)-f_W(q_W^*)
   \ge
   \frac{\|p_W\|}{2}\|q-q_W^*\|^2
   \quad(q\text{ in the unit ball}).
   \]

### Step 3: Stationarity, covariance, and sensitivity

[Barycentric.lean](ZeroOrderBounds/Barycentric.lean) proves the analytic
structure without assuming KKT machinery:

- `barycentricEnergy_add_tangent_eq` is the exact tangent identity;
- `minWeights_pos` proves all minimizing weights are positive;
- `minWeights_apply_eq` gives their explicit formula;
- `barycentric_covariance_equation` proves

  \[
  \left(I+\frac m{a^2}\Sigma_W\right)z_W=\mu_W.
  \]

[Covariance.lean](ZeroOrderBounds/Covariance.lean) defines `rowMean`,
`covariance`, and `perturbRow`. Audit `covariance_perturbRow_sub`,
`norm_covariance_le`, and `norm_covariance_perturbRow_sub_le`. The latter
proves

\[
 \|\Sigma_{W'}-\Sigma_W\|
 \le
 \frac{8\tau\|h\|}{m}.
\]

The constant 8 is weaker than the outline's 6, but the later slack absorbs it.

[OneRowSensitivity.lean](ZeroOrderBounds/OneRowSensitivity.lean) subtracts the
covariance equations, separates the unnormalized row blocks, and uses the
fixed coordinate sum to control normalization. Its headline theorem,
`hardOptimizer_perturbRow_separation`, is

\[
 \frac{\|h\|}{16a\sqrt m}
 \le
 \|q_W^*-q_{\operatorname{perturbRow}(W,j,h)}^*\|.
\]

Supporting targets are `norm_covariance_error_le`,
`norm_zBlock_perturbRow_sub_lower`, and
`norm_minPoint_perturbRow_sub_le_normalized`.

### Step 4: Intrinsic volume and exact affine sections

[IntrinsicVolume.lean](ZeroOrderBounds/IntrinsicVolume.lean) defines
`affineDim`, `intrinsicVolume`, and `IntrinsicBody`. A nonempty
zero-dimensional body has volume one; otherwise it is measured with Euclidean
Hausdorff measure in its affine dimension.

Audit:

- `intrinsicVolume_pos_of_nonempty_convex` and `intrinsicVolume_lt_top`;
- `affineDim_eq_of_positive_measure_subset`, preserving dimension under a
  positive full-dimensional truncation;
- `intrinsicVolume_le_of_subset_closedBall`, handling translated affine hulls;
- `intrinsicVolume_le_of_pairwise_dist_lt`, the diameter-volume bound.

[BallVolumeRatio.lean](ZeroOrderBounds/BallVolumeRatio.lean) inserts an
explicit cylinder into successive unit balls. `kappaReal_ratio_lower` proves

\[
 (2\sqrt m)^{-(m-k)}
 \le
 \frac{\kappa_m}{\kappa_k}.
\]

[AtomlessQuantile.lean](ZeroOrderBounds/AtomlessQuantile.lean) proves exact
upper-tail quantiles; the main endpoint is `exists_map_Ici_measure_eq`.

[QuantileSection.lean](ZeroOrderBounds/QuantileSection.lean) proves:

- `euclideanHausdorffMeasure_affineSection_eq_zero`, nullity of nonconstant
  level fibers;
- `exists_affineCap_euclideanHausdorffMeasure_eq`, an exact-volume cap;
- `exists_large_affineSection`, a section whose codimension-one volume is at
  least cap volume divided by \(2\tau\);
- `affineDim_affineSection_eq_sub_one_of_pos`, the exact dimension drop.

This branch justifies exact, rather than rounded, oracle answers.

### Step 5: Strategy model and fixed-function consistency

[OracleState.lean](ZeroOrderBounds/OracleState.lean) contains the
information-theoretic model:

- `DeterministicStrategy` has arbitrary maps `List ℝ → UnitBall m` for the
  next query and output. There is no continuity, computability, finite
  precision, time, memory, or linear-span restriction.
- `Consistent A ys W` states exact equality at every prefix-determined query.
- `RowBody` bundles nonempty compact convex row uncertainty.
- `rowProduct` is the Cartesian product of all row bodies.
- `ProductConsistent A ys rows` says every matrix in the current product
  reproduces the entire transcript.
- `OracleState` stores the transcript, row bodies, and this invariant.
- `ProductConsistent.append_of_rowsAnswerAt` preserves the invariant at a step.

This closes the fixed-function loophole: the final matrix is chosen after the
interaction, but it is one fixed matrix reproducing all previous answers.

### Step 6: One oracle transition and repeated queries

[OracleStep.lean](ZeroOrderBounds/OracleStep.lean) defines:

- `rowThreshold`, the exact upper \(1/(4m)\)-quantile on a nonconstant row;
- `Informative`, detecting a nonconstant row at the largest threshold;
- `exists_informativeStepResult`, which sections one row and lower-cuts the
  others;
- `exists_noninformativeStepResult`, which retains a constant equality witness;
- `StepResult`, recording exactness, containment, dimension, and volume loss;
- `oracleStep` and `oracleNextState`, choosing a valid result classically and
  preserving `ProductConsistent`.

The final proof needs only the `StepResult` fields. It does not require the
selected `oracleStep` to be definitionally the least-index witness built in
the informative existence proof.

[RepeatedQuery.lean](ZeroOrderBounds/RepeatedQuery.lean) proves that a
repeated query admits a vacuous noninformative transition.
`OracleState.exists_vacuousStepResult_of_repeated_query` is intentionally
existential: it does not claim equality with the opaque witness selected from
the unrefined `StepResult` type. This distinction does not affect the lower
bound.

### Step 7: Iteration and normalized-volume potential

[OracleRun.lean](ZeroOrderBounds/OracleRun.lean) iterates the transition:

- `oracleStateAt A T` is the state after exactly \(T\) rounds;
- `oracleStateAt_answers_length` proves the transcript length is \(T\);
- `oracleRowCount` counts selections of each row;
- `oracleStateAt_dim_eq` proves \(k_i=m-c_i\);
- `sum_oracleRowCount_le` proves \(\sum_i c_i\le T\);
- `oracleRun_final_budgets` exports the dimension and entropy budgets.

[VolumePotential.lean](ZeroOrderBounds/VolumePotential.lean) normalizes row
volume by \(\kappa_{k_i}\tau^{k_i}\). Audit this chain:

1. `productVolume_lower_of_oracle_steps`: every round keeps a product factor
   at least \(3/4\), while an informative round also pays \(1/(8m\tau)\).
2. `product_row_normalizers_le` and `normalized_product_lower`: powers of
   \(\tau\) cancel and the ball ratio charges at most \(2\sqrt m\) per lost
   dimension.
3. `entropy_sum_le_of_normalized_product`: taking logarithms gives

   \[
   \sum_i-\log\rho_i
   \le
   T\log\left(\frac{64}{3}m\sqrt m\right).
   \]

4. `volumePotential_of_oracle_steps` and `oracleRun_volumePotential` connect
   the abstract potential to the recursive state.

All logarithm arguments and real-volume denominators are proved positive.

### Step 8: Good row, indistinguishability, and final gap

[GoodRow.lean](ZeroOrderBounds/GoodRow.lean) combines the budgets under
\(1000T\le m^2\). `exists_good_row_quarter_radius` obtains

\[
 k_i\ge\frac{99}{100}m,
 \qquad
 \rho_i\ge m^{-k_i/4}.
\]

`IntrinsicBody.exists_pair_dist_ge_quarter` then finds \(w,w'\) with

\[
 \|w-w'\|
 \ge
 \frac{\tau}{2}m^{-1/4}.
\]

[Indistinguishability.lean](ZeroOrderBounds/Indistinguishability.lean)
extends these points to matrices agreeing in every other row:

- `exists_product_selections_perturbRow` constructs both matrices in the final
  product;
- `OracleState.exists_consistent_selection_with_gap_of_pair` combines exact
  consistency, sensitivity, and the shared strategy output;
- `OracleState.exists_consistent_selection_with_advertised_gap` selects one
  fixed instance with the strict gap.

[FinalGap.lean](ZeroOrderBounds/FinalGap.lean) supplies
`one_of_two_objective_gaps_of_sensitivity_scale` and the exact arithmetic
theorem `quarter_separation_gap_gt_advertised`:

\[
 \frac{a}{8192\Gamma^2m^3}
 =
 \frac{1}{163{,}840{,}000m^3}
 >
 \frac{1}{200{,}000{,}000m^3}.
\]

[Main.lean](ZeroOrderBounds/Main.lean) completes the assembly:

1. `exists_advertised_gap_of_final_budgets` extracts the good row.
2. `exists_advertised_gap_of_round_budgets` derives its hypotheses from \(T\).
3. `fixedHorizonLowerBound_strict` returns the exact transcript and fixed hard
   instance with all certificates.
4. `not_succeedsWithin_advertised` rules out error at most the same threshold
   on every consistent length-\(T\) hard instance.

## 5. Crosswalk to the manuscript

The Lean proof and
[value_oracle_accuracy.tex](zero_order_LB_tex/value_oracle_restructured_submission/value_oracle_accuracy.tex)
share this backbone:

| Shared step | Manuscript section | Lean modules |
|---|---|---|
| Max-linear hard family and support-polytope optimizer | “The hard family and its minimizers” | `HardFamily`, `ProjectionGeometry`, `Barycentric` |
| Exact Cartesian-product resisting oracle | “The adversarial exact-value oracle” | `OracleState`, `OracleStep` |
| Exact quantiles and large affine sections | Lemma “Quantiles and large affine sections” | `AtomlessQuantile`, `QuantileSection` |
| Dimension and normalized-volume accounting | “Dimension and volume accounting” | `BallVolumeRatio`, `VolumePotential`, `OracleRun` |

They then deliberately diverge:

- The manuscript uses \(T=O(m^2/\log m)\), linearly many good rows,
  Urysohn's inequality, a common wide direction, and simultaneous many-row
  perturbations. It obtains an \(m^{-1/2}\) objective gap.
- The Lean proof uses \(T=O(m^2)\), one good row, and one-row sensitivity. The
  single-row displacement is diluted by its barycentric weight and produces
  an \(m^{-3}\) objective gap.

This repository therefore does not kernel-check the manuscript's
Urysohn/common-direction/aggregate-width branch. The arguments share the same
first half but use materially different final separation mechanisms.

## 6. Model-compliance checklist

- **Exact real oracle:** transcripts are `List ℝ`; no finite answer alphabet.
- **Arbitrary adaptivity:** query and output maps have no regularity fields.
- **Domain fidelity:** both maps return `UnitBall m`.
- **Unqueried output allowed:** `output` is an independent arbitrary map.
- **One fixed function:** `ProductConsistent` gives simultaneous consistency.
- **Convexity and normalization:** `convexOn_hardObjective` and
  `hardObjective_zero`.
- **One-Lipschitz bound:** `hardObjective_lipschitzWith_one` from
  `Admissible W`.
- **Actual optimum:** `hardOptimizer_isMinOn` certifies the reference point.
- **Quantifier order:** `fixedHorizonLowerBound_strict` has
  \(\forall A\,\exists\mathtt{ys}\,\exists W\).
- **No output-as-query assumption:** the gap is at `A.output ys`.

## 7. Verification and trusted base

The toolchain is pinned by [lean-toolchain](lean-toolchain),
[lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json):

- Lean and Lake: `v4.32.0`, Lean commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- mathlib: `v4.32.0`, resolved commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`.

On 2026-07-14 these checks passed:

~~~sh
lake build
lake env lean --trust=0 ZeroOrderBounds/Main.lean
lake env lean --trust=0 ZeroOrderBounds.lean
~~~

The clean build completed 3,491 jobs. Every one of the 19 files under
`ZeroOrderBounds/` was also directly elaborated with `--trust=0`. The normal
build emits only nonsemantic style warnings in `IntrinsicVolume.lean` and
`QuantileSection.lean`.

A source scan found no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`,
`extern`, `partial`, `implemented_by`, `native_decide`, or `sorryAx` escape
hatch. The three `#print axioms` commands in `Main.lean` report exactly:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

These are standard Lean/classical dependencies. `Classical.choice` is expected
for minimum-norm points, exact quantiles, affine sections, and the
noncomputable resisting oracle.

`lake exe runLinter ZeroOrderBounds` is not a correctness check and currently
reports documentation/API-style findings. They add no proof assumptions and
do not affect `lake build` or kernel checking.
