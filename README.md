# Lean companion to *Closing the Oracle-Complexity Gap in Derivative-Free Convex Optimization*

This repository accompanies the manuscript
[*Closing the Oracle-Complexity Gap in Derivative-Free Convex Optimization: A Near-Quadratic Lower Bound from Exact Function Values*](zero_order_lower_bounds_manuscript.pdf).
It contains the manuscript sources and a Lean 4/mathlib formalization of a
deterministic exact-value oracle lower bound for convex optimization.

The results have different accuracy guarantees:

- **Manuscript:** $\Omega(d^2/\log d)$ queries at
  $\Theta(d^{-1/2})$ accuracy.
- **Lean:** $\Omega(d^2)$ queries at explicit $\Theta(d^{-3})$ accuracy, for
  even dimensions.

## Formally verified theorem

Write $d=2m$. For every $m\ge1000$, horizon $T$ satisfying

$$
1000T\le m^2,
$$

and every deterministic exact-value strategy run for exactly $T$ rounds, Lean
constructs a consistent transcript and an admissible convex, globally
one-Lipschitz max-linear objective with $f(0)=0$. It also certifies a minimizer
over the Euclidean unit ball and proves that the strategy's error is greater
than

$$
\frac{1}{200{,}000{,}000\,m^3}.
$$

Equivalently, for even $d\ge2000$, every horizon with $4000T\le d^2$ can be
defeated at accuracy

$$
\frac{1}{25{,}000{,}000\,d^3}.
$$

Strategies may depend arbitrarily on the complete exact-real transcript; no
continuity, finite-precision, linear-span, time, or memory restriction is
assumed.

The public statements in [`ZeroOrderBounds/Main.lean`](ZeroOrderBounds/Main.lean)
are:

- `ZeroOrderBounds.fixedHorizonLowerBound_strict`;
- `ZeroOrderBounds.fixedHorizonLowerBound`; and
- `ZeroOrderBounds.not_succeedsWithin_advertised`.

`SucceedsWithin` models exactly $T$ queries. The standard reduction from at
most $T$ queries uses padding and is not separately formalized.

## Why up to $d^{-3}$ accuracy?

The main result of the paper is the $\Omega(d^2)$ lower bound, and the overall proof structure for using $d^{-3}$ versus the manuscripts $d^{-1/2}$ accuracy are quite similar. The proofs share the hard family, exact resisting oracle, and normalized-volume
potential. The manuscript then uses Urysohn's mean-width inequality and
spherical averaging across many rows. The necessary convex-body, mean-width,
and rotationally invariant measure infrastructure is not available as a
ready-to-use result in Lean libraries, so formalizing that step would be a
substantially larger project project. For this verfication we thus use a simpler one-row sensitivity argument, which requires the order $d^{-3}$ accuracy to achieve our main near-quadratic lower-bound. 
Formal verification of the sharper $d^{-1/2}$ result is planned as future work, and will be added to this repository when completed.


## Repository layout

- [`zero_order_LB_tex/value_oracle_restructured_submission/`](zero_order_LB_tex/value_oracle_restructured_submission/)
  contains the manuscript and bibliography.
- [`ZeroOrderBounds/`](ZeroOrderBounds/) contains the Lean proof modules,
  separated into the hard family, projection and barycentric geometry,
  intrinsic volume and affine sections, oracle state and iteration, volume
  potential, sensitivity, indistinguishability, and final assembly.
- [`ZeroOrderBounds.lean`](ZeroOrderBounds.lean) is the library root. A normal
  `lake build` reaches the complete proof chain and the repeated-query sanity
  theorem.
- [`LEAN_PROOF_MAP.md`](LEAN_PROOF_MAP.md) gives the reviewer-facing proof map,
  module-by-module theorem cross-references, model audit, scope boundaries,
  and verification record.
- [`LEAN_FORMALIZATION_INSTRUCTIONS.md`](LEAN_FORMALIZATION_INSTRUCTIONS.md)
  and
  [`Lean-Zero-Order-Project-README.md`](Lean-Zero-Order-Project-README.md)
  record the formalization specification and proof architecture.
- [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json),
  and [`lean-toolchain`](lean-toolchain) pin the build environment.

## Building and checking the proof

Install [Elan](https://lean-lang.org/install/) if Lean is not already
available, then run from the repository root:

```bash
lake exe cache get
lake build
```

The cache only supplies compatible mathlib artifacts; project declarations are
still checked. For a fresh build, use:

```bash
lake clean
lake build
```

For a targeted strict check:

```bash
lake env lean --trust=0 ZeroOrderBounds/Main.lean
```

## Verification status and trusted base

Verified on 2026-07-14 with Lean `v4.32.0` and mathlib `v4.32.0`; exact
revisions are in [`lake-manifest.json`](lake-manifest.json). A clean build
completed 3,491 jobs, and all 19 project modules elaborated with `--trust=0`.
The source contains no `sorry`, `admit`, project-specific axioms, or
unsafe/opaque proof escape hatches. Remaining build warnings are stylistic.

The final `#print axioms` checks in `ZeroOrderBounds/Main.lean` report only:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/classical dependencies. See the
[Lean proof map](LEAN_PROOF_MAP.md) for the complete audit.

## References

- [Lean installation](https://lean-lang.org/install/)
- [Lean and mathlib project setup](https://leanprover-community.github.io/install/project.html)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
