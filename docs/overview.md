# Euclidean compact embedding

The `H¹` space is the closure of the graph of the gradient of compactly
supported `C¹` functions in the product of scalar and vector-valued `L²` spaces.
For a measurable set `K`, the subspace `h1On K` restricts the scalar component
to functions vanishing almost everywhere outside `K`.

When `K` is compact, a bounded family in `h1On K` has uniformly small `L²`
translations. Smoothing by a compactly supported kernel and applying
Arzelà–Ascoli gives the Fréchet–Kolmogorov compactness criterion. The resulting
compact operator is `h1OnToL2`. [Euclidean theorem](../RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/Rellich.lean).

The Lean 4.34.1 compatibility branch builds this Euclidean import closure.
Installation, the downstream example and the verification commands are in
the [README](../README.md). The complete manifold development and its API
documentation workflow are on the [Lean 4.29.1 branch](https://github.com/abenenson/rellich-kondrachov/tree/main).
