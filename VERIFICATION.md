# Verification record

Date: 2026-07-16

Toolchain:

- Lean `v4.32.0`
- Mathlib `v4.32.0`
- Comparator `v4.32.0` (`07bc4ea40f2266dcb861820a2ec1fa3244ed307f`)
- lean4export `4e7915201d3f9f04470d9eae002fa695f7cdc589`

## Verification boundary

[`Challenge.lean`](Challenge.lean) is the trusted, statement-only fixture. It
imports [`ZeroOrderBounds/Statement.lean`](ZeroOrderBounds/Statement.lean),
which exposes the vocabulary needed to state the result without importing the
final proof in `ZeroOrderBounds.Main`. Its single `sorry` is intentional and is
excluded from all production-source counts.

[`Solution.lean`](Solution.lean) repeats the challenge statement and delegates
the resisting-oracle conclusion to
`ZeroOrderBounds.fixedHorizonLowerBound_strict`. It also supplies explicit
certificates that the returned objective is normalized at zero, convex on the
whole ambient space, and globally one-Lipschitz. The configuration in
[`comparator/fixed_horizon_lower_bound.json`](comparator/fixed_horizon_lower_bound.json)
requires Comparator to establish that:

1. the challenge and solution declarations have the same statement;
2. the solution uses no axioms beyond `propext`, `Classical.choice`, and
   `Quot.sound`; and
3. Lean's kernel accepts the exported solution environment.

Comparator does not establish that this Lean statement is the manuscript's
headline theorem. [`formalization.yaml`](formalization.yaml) records the
alignment and the material divergence: Lean proves the even-dimensional
fixed-horizon result at order `d^-3` accuracy, not the manuscript's
all-dimensional order `d^-1/2` result.

## Local checks

Run from the repository root:

```bash
lake build
lake build Challenge Solution
lake env lean --trust=0 ZeroOrderBounds/Audit.lean
```

The following production-source scan must produce no output. It intentionally
excludes `Challenge.lean` and includes `Solution.lean`.

```bash
grep -R -n -E --include='*.lean' \
  '\b(sorry|admit|native_decide)\b|^[[:space:]]*(axiom|opaque|unsafe|extern|partial)\b|^[[:space:]]*@\[implemented_by' \
  ZeroOrderBounds.lean ZeroOrderBounds Solution.lean
```

On 2026-07-16 these checks passed. The exact axiom guards in
[`ZeroOrderBounds/Audit.lean`](ZeroOrderBounds/Audit.lean) reported only:

```text
[propext, Classical.choice, Quot.sound]
```

A local development run of Comparator with its explicitly unsandboxed fake
Landrun shim reported:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

That local run validates the Comparator configuration and kernel replay but is
not a security boundary. The sandboxed verification gate is
[`comparator.yml`](.github/workflows/comparator.yml). It starts from a fresh
Ubuntu 24.04 checkout, does not prebuild `Challenge` or `Solution`, builds
pinned verification tools, verifies Landrun filesystem denial with positive
and negative controls, applies an outer systemd network guard, and then runs
Comparator as the unprivileged runner user.
