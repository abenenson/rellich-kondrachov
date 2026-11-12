# Rellich–Kondrachov Overview

This project formalizes a compact Sobolev embedding theorem: on a compact Riemannian
manifold, the natural inclusion from `H¹` to `L²` is a compact operator.

## Organization

The development is organized in focused layers:

1. measure and `Lp` restriction/change-of-measure lemmas,
2. Euclidean `H¹` and translation-estimate API,
3. Fréchet–Kolmogorov and Euclidean compactness,
4. chart-local Sobolev transport and localization,
5. Riemannian volume specialization and the global compact embedding theorem.

This staged organization separates reusable library pieces from the final manifold theorem.

## Verification

The repository is pinned to Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.
CI builds the complete library with warnings treated as errors, then builds its API
documentation with the matching `doc-gen4` release. Each successful run uploads the
`api-docs` artifact, including pull requests and manual runs.

To build the API documentation locally after `lake build`, run
`bash scripts/build-docs.sh`. The output is in `public-docs/docs`.

Publishing is optional: after configuring GitHub Pages to use GitHub Actions, set
the repository variable `PUBLISH_DOCS` to `true` to deploy documentation on pushes
to `main`.
