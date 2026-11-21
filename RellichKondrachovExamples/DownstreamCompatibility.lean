/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

/-!
# Using the Euclidean Rellich theorem on the plane

The first example extracts a convergent `L²` subsequence from a bounded sequence with
common compact support. The second recovers the scalar and gradient representatives of a
compactly supported `C¹` test function from the Sobolev completion.

These examples exercise interfaces used by the public
[radial-window proof](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L518)
and [planar Sobolev model](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/PlanarSobolev.lean#L53).
-/

namespace RellichKondrachovExamples

noncomputable section

open Filter MeasureTheory
open scoped Topology
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

/-- The real Euclidean plane with its Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The measurable sets on the plane are its Borel sets. -/
local instance : MeasurableSpace Plane := borel Plane
/-- Identify the chosen measurable space with the Borel space. -/
local instance : BorelSpace Plane := ⟨rfl⟩
/-- Use the volume normalized by the Euclidean inner product. -/
local instance : MeasureSpace Plane := measureSpaceOfInnerProductSpace

/-- Compactness supplies a convergent image subsequence for any norm-bounded input sequence. -/
private theorem compact_image_subsequence {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) (hT : IsCompactOperator T)
    (u : ℕ → X) (R : ℝ) (hbound : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : Y, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n ↦ T (u (φ n))) atTop (𝓝 v) := by
  have hC : IsCompact (closure (T '' Metric.closedBall 0 R)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R
  have hmem (n : ℕ) : T (u n) ∈ closure (T '' Metric.closedBall 0 R) := by
    apply subset_closure
    exact ⟨u n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n, rfl⟩
  obtain ⟨v, _, φ, hφ, hv⟩ := hC.tendsto_subseq hmem
  exact ⟨v, φ, hφ, hv⟩

set_option maxHeartbeats 900000 in
/-- A uniformly bounded sequence of supported Sobolev functions has an `L²`-convergent
subsequence. The same compact set supports every term. -/
theorem exists_l2_subsequence {K : Set Plane} (hK : IsCompact K)
    (u : ℕ → h1On K hK.measurableSet) (R : ℝ) (hbound : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : Lp ℝ 2 (volume : Measure Plane), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ h1OnToL2 K hK.measurableSet (u (φ n))) atTop (𝓝 v) := by
  exact compact_image_subsequence (X := h1On K hK.measurableSet)
    (Y := Lp ℝ 2 (volume : Measure Plane)) (h1OnToL2 (E := Plane) K hK.measurableSet)
    (isCompactOperator_h1OnToL2 (E := Plane) hK hK.measurableSet) u R hbound

/-- A compactly supported `C¹` function determines a Sobolev element whose two projections
agree almost everywhere with the function and its classical gradient. -/
theorem exists_h1_representative (f : C1c (E := Plane)) :
    ∃ u : h1 (E := Plane) (μ := volume),
      (h1ToL2 (μ := volume) u : Plane → ℝ) =ᵐ[volume] f.1 ∧
      (h1ToL2Grad (μ := volume) u : Plane → Plane) =ᵐ[volume] grad f.1 := by
  let g := graph (E := Plane) (μ := volume)
  refine ⟨⟨g f, (LinearMap.range g).le_topologicalClosure ⟨f, rfl⟩⟩, ?_, ?_⟩
  · exact (memLp_of_mem_C1c (μ := volume) f.2).coeFn_toLp
  · exact (memLp_grad_of_mem_C1c (μ := volume) f.2).coeFn_toLp

end

end RellichKondrachovExamples
