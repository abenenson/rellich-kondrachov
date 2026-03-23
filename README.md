# rellich-kondrachov

Lean 4 proof of the **Rellich–Kondrachov compact embedding theorem**: the Sobolev embedding H¹ → L² is compact on compact Riemannian manifolds.

## Main result

```lean
-- The H¹ → L² embedding is a compact operator on compact Riemannian manifolds
theorem FiniteChartData.isCompactOperator_h1ToL2_of_summands ...
```

## Proof strategy

1. **Euclidean heart** (`Euclidean/Rellich`): for a fixed compact set K ⊆ ℝⁿ, the inclusion H¹ → L² restricted to functions supported in K is compact. Proved via Fréchet–Kolmogorov + H¹ translation estimate.
2. **Manifold glue** (`Manifold/RellichKondrachov`): package the chart-level compactness into a global compact operator using finite chart decomposition.
3. **Riemannian specialisation** (`Manifold/RellichKondrachovRiemannian`): instantiate for Riemannian manifolds with Levi-Civita volume measure.

## Dependencies

Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4). No external dependencies.

## Mathlib upstreaming

This is intended as a Mathlib contribution. The proof is sorry-free.

## References

- K. O. Friedrichs, "On the boundary-value problems of the theory of elasticity", 1947
- F. Rellich, "Ein Satz über mittlere Konvergenz", 1930
- T. Kondrachov, "Sur certaines propriétés des fonctions...", 1945
