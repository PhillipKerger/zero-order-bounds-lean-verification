# Lean companion to *Closing the Oracle-Complexity Gap in Derivative-Free Convex Optimization*

This repository accompanies the manuscript
[*Closing the Oracle-Complexity Gap in Derivative-Free Convex Optimization: A Near-Quadratic Lower Bound from Exact Function Values*](zero_order_lower_bounds_manuscript.pdf).
It contains Lean 4/mathlib proofs of deterministic exact-value oracle lower
bounds for convex optimization.

Two endpoints are preserved and independently auditable:

- the top-level [`ZeroOrderBounds/`](ZeroOrderBounds/) development contains
  the original, simpler even-dimensional `d⁻³`-accuracy theorem; and
- [`FullDMinusOneHalfAccuracy/`](FullDMinusOneHalfAccuracy/) fully verifies
  the paper's sharper deterministic `d⁻¹ᐟ²`-accuracy lower bound, including
  its spherical-averaging, Brunn--Minkowski, and intrinsic Urysohn machinery.

Here “fully verifies” refers to the paper's deterministic lower-bound result;
the separate upper-bound and transfer results listed under
[Scope boundary](#scope-boundary) remain outside the formalization.

## Full `d⁻¹ᐟ²`-accuracy theorem

Write `d = 2m`, and let

$$
\varepsilon_m=\frac{10^{-7}}{\sqrt{2m}}.
$$

For every positive `m`, every exact horizon `T` satisfying

$$
T \le \frac{m^2}{100\log(e m)},
$$

and every deterministic exact-value strategy, Lean constructs a length-`T`
transcript and an admissible max-affine objective for which the strategy's
strict objective error exceeds `ε_m`.  The conclusion explicitly certifies:

- normalization at zero;
- convexity and global one-Lipschitzness;
- consistency with every exact oracle answer;
- a minimizer in the Euclidean unit ball; and
- the strict `10⁻⁷ / √d` gap.

The production declaration is
`ZeroOrderBounds.AccuracyImprovement.fixedHorizonSqrtLowerBound_strict` in
[`FullDMinusOneHalfAccuracy/Main.lean`](FullDMinusOneHalfAccuracy/Main.lean).  Its proof
formalizes the manuscript's aggregate-width argument, including spherical
averaging, finite Haar averages, intrinsic Urysohn, and a proof of
Brunn--Minkowski in every positive Euclidean dimension from the
one-dimensional Borell--Brascamp--Lieb transport argument.  The standalone
unconditional geometric endpoints are collected in
[`FullDMinusOneHalfAccuracy/UrysohnMain.lean`](FullDMinusOneHalfAccuracy/UrysohnMain.lean).

The following additional wrappers are checked in Lean:

- [`FullDMinusOneHalfAccuracy/StoppingStrategy.lean`](FullDMinusOneHalfAccuracy/StoppingStrategy.lean)
  proves exact padding for transcript-dependent strategies which may stop
  after at most `T` queries.
- [`FullDMinusOneHalfAccuracy/QueryBudget.lean`](FullDMinusOneHalfAccuracy/QueryBudget.lean)
  defines `floor(m² / (100 log(e m)))`; [`FullDMinusOneHalfAccuracy/Main.lean`](FullDMinusOneHalfAccuracy/Main.lean)
  rules out success at that budget and proves that the first horizon outside
  the ruled-out range is greater than
  `d² / (800 log(d+1))` for `d = 2m`.
- [`FullDMinusOneHalfAccuracy/OddMain.lean`](FullDMinusOneHalfAccuracy/OddMain.lean)
  projects an arbitrary strategy in dimension `2m+1` to the even block and
  lifts the hard objective, preserving a strict `10⁻⁷ / √(2m+1)` gap.  It
  also rules out every exact horizon through the floored core budget and
  proves the odd-dimensional rate
  `d² / (1800 log(d+1)) < paperQueryBudget m + 1`.
- [`FullDMinusOneHalfAccuracy/ScaledMain.lean`](FullDMinusOneHalfAccuracy/ScaledMain.lean)
  transports the fixed-horizon result to a ball of radius `R` and
  `L`-Lipschitz objectives, with gap `(L R)ε_m`, and proves monotonicity for
  smaller target errors.
- [`FullDMinusOneHalfAccuracy/PaperStopping.lean`](FullDMinusOneHalfAccuracy/PaperStopping.lean)
  supplies transcript-dependent at-most-query models and padding theorems for
  both the odd ambient space and the scaled radius-`R` space.  It rules out
  the floored budget in odd dimension and, in the scaled even model, for every
  target error at most `(L R)ε_m`.

These are composable declarations.  Even and odd dimensions both have
explicit floor/rate and at-most-query theorems, and the scaled even model has
fixed- and at-most-horizon theorems.  The repository does not claim a single
odd-dimensional theorem carrying the radius/Lipschitz scaling parameters at
once.

## Preserved `d⁻³` theorem

The original endpoint remains unchanged.  For `m ≥ 1000`, `d = 2m`, and
`1000 T ≤ m²`, it defeats every exact-`T` deterministic strategy with strict
error greater than

$$
\frac{1}{200{,}000{,}000\,m^3}
=\frac{1}{25{,}000{,}000\,d^3}.
$$

Its public declarations remain
`ZeroOrderBounds.fixedHorizonLowerBound_strict`,
`ZeroOrderBounds.fixedHorizonLowerBound`, and
`ZeroOrderBounds.not_succeedsWithin_advertised` in
[`ZeroOrderBounds/Main.lean`](ZeroOrderBounds/Main.lean).

This top-level proof is retained as a smaller independent verification target:
its one-row sensitivity argument needs substantially less convex-geometric
machinery than the full `d⁻¹ᐟ²` proof.

Both developments allow arbitrary dependence on the complete exact-real
transcript; they impose no continuity, finite-precision, linear-span, time, or
memory restriction on the strategy.

## Repository layout

- [`zero_order_LB_tex/value_oracle_restructured_submission/`](zero_order_LB_tex/value_oracle_restructured_submission/)
  contains the manuscript source and bibliography.  The sharper proof is in
  [`value_oracle_accuracy.tex`](zero_order_LB_tex/value_oracle_restructured_submission/value_oracle_accuracy.tex).
- [`ZeroOrderBounds/`](ZeroOrderBounds/) and [`ZeroOrderBounds.lean`](ZeroOrderBounds.lean)
  contain the original `d⁻³` proof.
- [`FullDMinusOneHalfAccuracy/`](FullDMinusOneHalfAccuracy/) and
  [`FullDMinusOneHalfAccuracy.lean`](FullDMinusOneHalfAccuracy.lean) contain
  the fully verified `d⁻¹ᐟ²` proof, its convex geometry, oracle endgame, and
  public wrappers.  The implementation map and scope ledger are in
  [`FullDMinusOneHalfAccuracy/PLAN.md`](FullDMinusOneHalfAccuracy/PLAN.md).
- [`Challenge-d-3-accuracy.lean`](Challenge-d-3-accuracy.lean),
  [`Solution.lean`](Solution.lean), and
  [`comparator/fixed_horizon_lower_bound.json`](comparator/fixed_horizon_lower_bound.json)
  audit the simpler `d⁻³` endpoint.
- [`FullDMinusOneHalfAccuracy/Challenge-full-d-1-2-accuracy.lean`](FullDMinusOneHalfAccuracy/Challenge-full-d-1-2-accuracy.lean),
  [`FullDMinusOneHalfAccuracy/Solution.lean`](FullDMinusOneHalfAccuracy/Solution.lean),
  [`FullDMinusOneHalfAccuracy/Audit.lean`](FullDMinusOneHalfAccuracy/Audit.lean), and
  [`FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json`](FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json)
  audit the full `d⁻¹ᐟ²` endpoint.
- [`formalization.yaml`](formalization.yaml) records source alignment and the
  exact verified scope; [`VERIFICATION.md`](VERIFICATION.md) records the
  reproducible checks.

## Build and verification

Install [Elan](https://lean-lang.org/install/), then run from the repository
root:

```bash
lake exe cache get
lake build ZeroOrderBounds
lake build FullDMinusOneHalfAccuracy
lake build 'Challenge-d-3-accuracy' Solution
lake build 'FullDMinusOneHalfAccuracy.«Challenge-full-d-1-2-accuracy»' \
  FullDMinusOneHalfAccuracy.Solution
```

The cache supplies compatible mathlib artifacts; all project declarations are
still elaborated and kernel-checked.  The load-bearing trust-zero checks are:

```bash
lake env lean --trust=0 ZeroOrderBounds/Main.lean
lake env lean --trust=0 ZeroOrderBounds/Audit.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/BrunnMinkowskiInduction.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/Main.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/OddMain.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/ScaledMain.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/PaperStopping.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/Audit.lean
```

With the pinned Comparator executable available locally, run both statement
and axiom comparisons:

```bash
lake env comparator comparator/fixed_horizon_lower_bound.json
lake env comparator FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json
```

The [`Comparator` workflow](.github/workflows/comparator.yml) performs the
same comparisons and kernel replay in a pinned sandboxed environment.  See
[`VERIFICATION.md`](VERIFICATION.md) for the trust boundary and the exact
production-source scan.

The improved production endpoint's guarded audit permits only:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/classical dependencies.  Neither development uses a
project-specific axiom or a production `sorry`/`admit`.

## Scope boundary

The paper's deterministic `d⁻¹ᐟ²` lower-bound result and its load-bearing
geometry are fully formalized.  The repository does **not** formalize the
Protasov upper bound, the resulting two-sided `widetildeTheta(d²)` claim, the
polynomial-accuracy upper corollary, or the mixed-integer transfer.

## References

- [Lean installation](https://lean-lang.org/install/)
- [Lean and mathlib project setup](https://leanprover-community.github.io/install/project.html)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
