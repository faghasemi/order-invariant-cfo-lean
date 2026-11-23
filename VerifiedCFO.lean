import Lax977378Proofs
import Lean
/-!
# Order-invariant CFO on bounded-degree graphs

This file links the local Lax submission into a single ordinary Lean theorem.
Lax stores statements and proofs in separate packages. For each statement
used below, the linker replaces its occurrence in the proof term by the
registered implementation and asks the kernel to check the resulting
declaration. The last command checks the axioms of the linked theorem.

From the submission's `proofs` directory after building the packages, run
`lake --packages=.lake/package-overrides.json env lean ../../VerifiedCFO.lean`.
-/

open Lean Elab Command

private def implementations : List (Name × Name) := [
  (`Lax977378.Blocks.interval,`Lax977378Proofs.interval),
  (`Lax977378.Blocks.outerIntervals,`Lax977378Proofs.outerIntervals),
  (`Lax977378.CallAgreement.compareReps,`Lax977378Proofs.CallAgreement.compareReps),
  (`Lax977378.CallAgreement.lowerRanks,`Lax977378Proofs.CallAgreement.lowerRanks),
  (`Lax977378.Catalogue.catalogue,`Lax977378Proofs.Catalogue.catalogue),
  (`Lax977378.CheckedEntries.selectEntries,`Lax977378Proofs.CheckedEntries.selectEntries),
  (`Lax977378.Collapse.relativeCollapse,`Lax977378Proofs.relativeCollapse),
  (`Lax977378.Collapse.collapse,`Lax977378Proofs.collapse),
  (`Lax977378.ColouredRun.colouredRun,`Lax977378Proofs.ColouredRun.colouredRun),
  (`Lax977378.ColouredTypes.colouredTypes,`Lax977378Proofs.ColouredTypes.colouredTypes),
  (`Lax977378.CommonPalette.uniform,`Lax977378Proofs.CommonPalette.uniform),
  (`Lax977378.Collapse.comparison,`Lax977378Proofs.Comparison.comparison),
  (`Lax977378.ContextLabels.finiteLabels,`Lax977378Proofs.ContextLabels.finiteLabels),
  (`Lax977378.CountParameters.countTestValue,`Lax977378Proofs.CountParameters.countTestValue),
  (`Lax977378.CountParameters.fixedParameters,`Lax977378Proofs.CountParameters.fixedParameters),
  (`Lax977378.CountParameters.parameters,`Lax977378Proofs.CountParameters.parameters),
  (`Lax977378.CoverReplay.orderFromCover,`Lax977378Proofs.CoverReplay.orderFromCover),
  (`Lax977378.Endpoints.twoCentres,`Lax977378Proofs.Endpoints.twoCentres),
  (`Lax977378.Endpoints.admissible,`Lax977378Proofs.Endpoints.admissible),
  (`Lax977378.Extraction.extract,`Lax977378Proofs.Extraction.extract),
  (`Lax977378.FiniteTests.finiteTests,`Lax977378Proofs.FiniteTests.finiteTests),
  (`Lax977378.InitialLevel.initialRecords,`Lax977378Proofs.InitialLevel.initialRecords),
  (`Lax977378.LocalCalls.commonCalls,`Lax977378Proofs.LocalCalls.commonCalls),
  (`Lax977378.LocalCalls.innerCalls,`Lax977378Proofs.LocalCalls.innerCalls),
  (`Lax977378.LocalCover.coverCalls,`Lax977378Proofs.LocalCover.coverCalls),
  (`Lax977378.LocalNames.names,`Lax977378Proofs.LocalNames.names),
  (`Lax977378.MarkedSets.moveStages,`Lax977378Proofs.MarkedSets.moveStages),
  (`Lax977378.OrdinaryCalls.untagged,`Lax977378Proofs.OrdinaryCalls.untagged),
  (`Lax977378.Planting.plant,`Lax977378Proofs.Planting.plant),
  (`Lax977378.RecordTests.recordTest,`Lax977378Proofs.RecordTests.recordTest),
  (`Lax977378.Collapse.records,`Lax977378Proofs.Records.records),
  (`Lax977378.Refinement.levelStep,`Lax977378Proofs.Refinement.levelStep),
  (`Lax977378.Replay.assemble,`Lax977378Proofs.Replay.assemble),
  (`Lax977378.Representatives.representatives,`Lax977378Proofs.Representatives.representatives),
  (`Lax977378.Reservoir.reserve,`Lax977378Proofs.Reservoir.reserve),
  (`Lax977378.RunReplay.runReplay,`Lax977378Proofs.RunReplay.runReplay),
  (`Lax977378.Separation.separated,`Lax977378Proofs.separated),
  (`Lax977378.Separation.extendColouring,`Lax977378Proofs.extendColouring),
  (`Lax977378.SourceRecord.sourceRecord,`Lax977378Proofs.SourceRecord.sourceRecord),
  (`Lax977378.SourceRun.construct,`Lax977378Proofs.SourceRun.construct),
  (`Lax977378.SourceTables.sourceTables,`Lax977378Proofs.SourceTables.sourceTables),
  (`Lax977378.Stage.refineBlocks,`Lax977378Proofs.Stage.refineBlocks),
  (`Lax977378.TableFacts.facts,`Lax977378Proofs.TableFacts.facts),
  (`Lax977378.TagSafety.ordinaryCalls,`Lax977378Proofs.TagSafety.ordinaryCalls),
  (`Lax977378.TargetOrder.targetOrder,`Lax977378Proofs.TargetOrder.targetOrder),
  (`Lax977378.TargetWindow.targetWindow,`Lax977378Proofs.TargetWindow.targetWindow),
  (`Lax977378.Threshold.uniformGap,`Lax977378Proofs.uniformGap),
  (`Lax977378.Transport.transport,`Lax977378Proofs.Transport.transport),
  (`Lax977378.Types.uniqueTypes,`Lax977378Proofs.Types.uniqueTypes),
  (`Lax977378.Window.exactBall,`Lax977378Proofs.Window.exactBall),
  (`Lax977378.WindowColour.precolour,`Lax977378Proofs.WindowColour.precolour),
  (`Lax977378.WindowMap.matchBall,`Lax977378Proofs.WindowMap.matchBall)]

private partial def closeProof (n : Name) : CoreM Name := do
  if let some (_,p) := implementations.find? (fun pair => pair.1 == n) then
    return ← closeProof p
  if !(← collectAxioms n).any (fun ax => `Lax977378 |>.isPrefixOf ax) then return n
  let dest := (`IndependentOrderKernel).append n
  if (← getEnv).contains dest then return dest
  let ci ← getConstInfo n
  let some proof := ci.value? (allowOpaque := true) | throwError "missing proof for {n}"
  let mut lookup : NameMap Name := {}
  for dep in proof.getUsedConstants do
    let actual ← closeProof dep
    if actual != dep then lookup := lookup.insert dep actual
  let body := proof.replace fun e => match e with
    | .const id ls => (lookup.find? id).map fun v => .const v ls
    | _ => none
  match ci with
  | .thmInfo t => addDecl (.thmDecl {t with name := dest, value := body})
  | .defnInfo t => addDecl (.defnDecl {t with name := dest, value := body})
  | _ => throwError "unexpected declaration {n}"
  return dest

set_option maxHeartbeats 0 in
run_cmd do
  let n ← liftCoreM (closeProof `Lax977378.Collapse.collapse)
  let axs ← collectAxioms n
  unless axs.all (fun a => [`propext,`Classical.choice,`Quot.sound].contains a) do
    throwError "unexpected axioms {axs}"


namespace VerifiedCFO
open Lax977378.Logic

/-- Every globally order-invariant CFO sentence has an order-free FO
equivalent on any fixed bounded-degree class of finite coloured graphs. -/
theorem orderInvariantCFO_in_FO {c d : Nat} (C : Graph c → Prop)
    (bounded : ∀ G, C G → G.Bounded d) (f : Formula c) (legal : Legal [] f)
    (inv : ∀ G : Graph c, ∀ a b, Holds G a f ↔ Holds G b f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ o, Holds G o f ↔ Unordered G φ :=
  IndependentOrderKernel.Lax977378Proofs.collapse C bounded f legal inv

#print axioms orderInvariantCFO_in_FO

end VerifiedCFO
