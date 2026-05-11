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
The public CI uses `leanprover/lean-action` and docgen.
