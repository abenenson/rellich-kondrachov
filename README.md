# Euclidean Rellich–Kondrachov compactness

[![Euclidean Rellich CI](https://github.com/abenenson/rellich-kondrachov/actions/workflows/lean_action_ci.yml/badge.svg?branch=compat%2Feuclidean-lean-v4.34.1)](https://github.com/abenenson/rellich-kondrachov/actions/workflows/lean_action_ci.yml?query=branch%3Acompat%2Feuclidean-lean-v4.34.1)

On a finite-dimensional real inner-product space, the `H¹ → L²` inclusion for
functions supported in a fixed compact set is a compact operator. This branch
provides the Euclidean theorem on **Lean 4.34.1** with Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete compact Riemannian
manifold development uses Lean 4.29.1 on [main](https://github.com/abenenson/rellich-kondrachov/tree/main).

## Use from another project

Add the dependency to a `lakefile.lean` using the same Lean and Mathlib pins.

```lean
require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @ "compat/euclidean-lean-v4.34.1"
```

Run `lake update rellich-kondrachov` and retain the resolved revision in
`lake-manifest.json`. Projects applying the `openai/math` compatibility patch
can remove that patch step when using this branch. The focused import and
theorem name are available directly.

```lean
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

#check h1OnToL2
#check isCompactOperator_h1OnToL2
```

The theorem takes a compactness proof and a measurability proof for the
fixed support set. The [downstream example](RellichKondrachovExamples/DownstreamCompatibility.lean)
uses it to extract an L²-convergent subsequence from a bounded planar H¹ sequence.

## Build and verification

```sh
python3 scripts/fetch-euclidean-cache.py
lake --wfail build
lake --wfail build RellichKondrachovExamples
lake env lean -DwarningAsError=true scripts/CheckEuclidean.lean
```

The default import builds the Euclidean theorem and its local prerequisites.
Verification checks the imported declarations with the Mathlib environment
linters and traces their axioms. The manifold modules are outside this branch's
default build. The [overview](docs/overview.md) describes the supported proof.

## Attribution

Adam Benenson authored the original compact embedding formalization. This
branch adapts the Apache-2.0 compatibility patch from `openai/math`, which
uses the same theorem in a number-theory proof. The source files retain their
copyright and license notices. [Pinned compatibility patch](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/patches/rellich-kondrachov-lean4341.patch) · [Downstream proof](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L529).
