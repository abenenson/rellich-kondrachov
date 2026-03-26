# rellich-kondrachov

Lean 4 proof of the **Rellich–Kondrachov compact embedding theorem**: the Sobolev embedding H¹ → L² is compact on compact Riemannian manifolds.

> **Build status:** Verified on Lean v4.29.0-rc7 with Mathlib. Zero sorries. Mathlib upstreaming candidate.


## Main result

```lean
theorem isCompactOperator_h1ToL2_riemannianVolume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [I.Boundaryless] [T3Space M] [CompactSpace M] :
    IsCompactOperator fun x : ↥(h1 (I := I) (μ := riemannianVolumeMeasure (I := I) (M := M))) =>
      h1ToL2 (I := I) (μ := riemannianVolumeMeasure (I := I) (M := M)) x
```

## Proof strategy

1. **Euclidean heart** (`Euclidean/Rellich`): for a fixed compact set K ⊆ ℝⁿ, the H¹ → L² inclusion restricted to functions supported in K is compact. Proved via the Fréchet–Kolmogorov compactness criterion, using the H¹ translation estimate `‖τₐu − u‖₂ ≤ ‖a‖ · ‖∇u‖₂`.
2. **Manifold glue** (`Manifold/RellichKondrachov`): given a finite atlas, the global H¹ → L² map is a finite sum of chart contributions; compactness of each summand implies compactness of the sum.
3. **Riemannian specialisation** (`Manifold/RellichKondrachovRiemannian`): instantiate for compact Riemannian manifolds with Levi-Civita volume measure.

## Dependencies

Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4). No external dependencies.

## Mathlib upstreaming

This is intended as a Mathlib contribution. The proof is sorry-free. Target namespace: `Mathlib.Geometry.Manifold.Sobolev`.

## References

- F. Rellich, "Ein Satz über mittlere Konvergenz", *Nachrichten der Akademie der Wissenschaften in Göttingen*, 1930
- V. I. Kondrachov, "Sur certaines propriétés des fonctions dans l'espace Lp", *Doklady Akademii Nauk SSSR*, 1945
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §5.7
