# Verification record

Date: 2026-07-17

Toolchain:

- Lean `v4.32.0`
- Mathlib `v4.32.0`
- Comparator `v4.32.0` (`07bc4ea40f2266dcb861820a2ec1fa3244ed307f`)
- lean4export `4e7915201d3f9f04470d9eae002fa695f7cdc589`

Exact dependency revisions are pinned in [`lean-toolchain`](lean-toolchain),
[`lake-manifest.json`](lake-manifest.json), and the
[`Comparator` workflow](.github/workflows/comparator.yml).

## Verification boundaries

### Original `d⁻³` endpoint

[`Challenge-d-3-accuracy.lean`](Challenge-d-3-accuracy.lean) is the
statement-only fixture for
`ZeroOrderBounds.fixedHorizonLowerBound_strict`.  It imports the
final-proof-independent vocabulary in
[`ZeroOrderBounds/Statement.lean`](ZeroOrderBounds/Statement.lean) and contains
one intentional `sorry`.

[`Solution.lean`](Solution.lean) repeats that statement and delegates to the
production theorem.  The Comparator configuration is
[`comparator/fixed_horizon_lower_bound.json`](comparator/fixed_horizon_lower_bound.json).

### Full `d⁻¹ᐟ²` endpoint

[`FullDMinusOneHalfAccuracy/Challenge-full-d-1-2-accuracy.lean`](FullDMinusOneHalfAccuracy/Challenge-full-d-1-2-accuracy.lean)
is the statement-only fixture for the even-dimensional exact-horizon theorem.  It
imports [`FullDMinusOneHalfAccuracy/Statement.lean`](FullDMinusOneHalfAccuracy/Statement.lean),
which defines only the public vocabulary and accuracy constant, and contains
one intentional `sorry`.

[`FullDMinusOneHalfAccuracy/Solution.lean`](FullDMinusOneHalfAccuracy/Solution.lean)
repeats the challenge declaration verbatim and delegates to
`ZeroOrderBounds.AccuracyImprovement.fixedHorizonSqrtLowerBound_strict` in
[`FullDMinusOneHalfAccuracy/Main.lean`](FullDMinusOneHalfAccuracy/Main.lean).  The compared
proposition includes exact transcript length, row admissibility,
normalization, convexity, global one-Lipschitzness, exact consistency, a
certified unit-ball minimizer, and the strict `10⁻⁷ / sqrt(2m)` gap.

The configuration
[`FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json`](FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json)
requires Comparator to establish that:

1. challenge and solution declarations have the same statement;
2. the solution uses no axioms beyond `propext`, `Classical.choice`, and
   `Quot.sound`; and
3. Lean's kernel accepts the exported solution environment.

[`FullDMinusOneHalfAccuracy/Audit.lean`](FullDMinusOneHalfAccuracy/Audit.lean) separately
pins the axiom output for the Euclidean Brunn--Minkowski family, unconditional
intrinsic Urysohn and row consequence, production theorem, solution wrapper,
fixed-horizon and at-most-budget impossibility, explicit even and odd rates,
scaled public endpoints, and the odd/scaled stopping-rate endpoints in
[`FullDMinusOneHalfAccuracy/PaperStopping.lean`](FullDMinusOneHalfAccuracy/PaperStopping.lean).

## Local checks

Run from the repository root:

```bash
lake exe cache get

# Preserved endpoint
lake build ZeroOrderBounds
lake build 'Challenge-d-3-accuracy' Solution
lake env lean --trust=0 ZeroOrderBounds/Main.lean
lake env lean --trust=0 ZeroOrderBounds/Audit.lean

# Full paper-accuracy endpoint and Comparator pair
lake build FullDMinusOneHalfAccuracy
lake build 'FullDMinusOneHalfAccuracy.«Challenge-full-d-1-2-accuracy»' \
  FullDMinusOneHalfAccuracy.Solution
lake env lean --trust=0 FullDMinusOneHalfAccuracy/BrunnMinkowskiInduction.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/UrysohnAssembly.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/UrysohnMain.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/Main.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/OddMain.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/ScaledMain.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/PaperStopping.lean
lake env lean --trust=0 FullDMinusOneHalfAccuracy/Audit.lean
```

The following production-source scan must produce no output.  It excludes the
two statement-only challenge fixtures but includes both solution wrappers.

```bash
rg -n \
  '\b(sorry|admit|native_decide)\b|^[[:space:]]*(axiom|opaque|unsafe|extern|partial)\b|^[[:space:]]*@\[implemented_by' \
  ZeroOrderBounds.lean ZeroOrderBounds Solution.lean \
  FullDMinusOneHalfAccuracy.lean FullDMinusOneHalfAccuracy \
  -g '*.lean' \
  -g '!Challenge-d-3-accuracy.lean' \
  -g '!Challenge-full-d-1-2-accuracy.lean'
```

The guarded axiom checks report only:

```text
[propext, Classical.choice, Quot.sound]
```

With the pinned Comparator binary available as `comparator`, run:

```bash
lake env comparator comparator/fixed_horizon_lower_bound.json
lake env comparator FullDMinusOneHalfAccuracy/comparator/d_sqrt_lower_bound.json
```

The local executable name is only a convenience; CI builds Comparator and
lean4export from the exact revisions listed above and invokes those binaries
by absolute path.

On 2026-07-17, local development runs of both configurations with those pinned
binaries reported:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

Those local runs used Comparator's explicitly unsandboxed development Landrun
shim.  They validate statement comparison, the axiom allowlists, export, and
kernel replay, but they are not the filesystem/network security boundary.

## Sandboxed CI gate

[`comparator.yml`](.github/workflows/comparator.yml) starts from a fresh Ubuntu
24.04 checkout, does not prebuild either challenge or solution, builds the
pinned verification tools, verifies Landrun filesystem denial with positive
and negative controls, applies an outer systemd network guard, and runs both
Comparator configurations as the unprivileged runner user.

Comparator audits the narrow fixed-horizon statements.  The production tree
also contains checked at-most-query, integer floor/rate, odd-dimensional, and
radius/Lipschitz wrappers, including odd and scaled stopping models; their
exact scope is catalogued in
[`FullDMinusOneHalfAccuracy/PLAN.md`](FullDMinusOneHalfAccuracy/PLAN.md) and
[`formalization.yaml`](formalization.yaml).

## Claim boundary

These checks verify the deterministic lower-bound declarations described
above.  They do not certify the manuscript's Protasov upper bound, two-sided
`widetildeTheta(d²)` conclusion, polynomial-accuracy upper corollary, or
mixed-integer transfer; those results are not formalized in this repository.
