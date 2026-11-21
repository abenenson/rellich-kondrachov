/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import RellichKondrachov
import RellichKondrachovExamples.DownstreamCompatibility
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter.Lint

/-! Check the imported Euclidean declarations, including their transitive axiom dependencies. -/

#lint docBlame docBlameThm in RellichKondrachov
#lint docBlame docBlameThm in RellichKondrachovExamples

open Lean in
run_cmd do
  let library ← Elab.Command.liftCoreM <|
    Batteries.Tactic.Lint.getDeclsInPackage `RellichKondrachov
  let examples ← Elab.Command.liftCoreM <|
    Batteries.Tactic.Lint.getDeclsInPackage `RellichKondrachovExamples
  let declarations := library ++ examples
  let entry :=
    ``RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2
  for target in #[entry, ``RellichKondrachovExamples.exists_l2_subsequence,
      ``RellichKondrachovExamples.exists_h1_representative] do
    unless declarations.contains target do
      throwError "Missing expected declaration {target}"
  for decl in declarations do
    let axioms ← collectAxioms decl
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{decl} depends on unexpected axiom {axiomName}"
  logInfo m!"Checked transitive axioms of {declarations.size} declarations."
