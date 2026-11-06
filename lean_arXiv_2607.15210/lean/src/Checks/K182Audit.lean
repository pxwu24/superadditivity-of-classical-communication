import Dimension182.K182Dual
import Dimension182.K182Numerics
import Dimension182.K182Entropy
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-!
Audit every theorem declared in the new certificate modules, including
private/generated helper theorems. This checks proof integrity, not that
the manuscript's entire analytic argument has been formalized.

The final entropy theorem below has an explicit minimizer-shape hypothesis.
The axiom audit must not be interpreted as discharging that hypothesis.
-/

#check ProjectionChannels.K182.normalized_coordinate_le_L
#check ProjectionChannels.K182.certified_entropy_gap
#check ProjectionChannels.K182.entropy_gap_of_one_high_minimizer
#check ProjectionChannels.K182.eventual_gap_of_one_high_minimizer

open Lean in
run_elab do
  let projectModules : Array Name := #[`Dimension182.K182Dual, `Dimension182.K182Numerics, `Dimension182.K182Entropy]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut projectAxioms : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if let some mi := env.getModuleIdxFor? name then
      if projectModules.contains env.allImportedModuleNames[mi.toNat]! then
        if ci.isTheorem then
          names := names.push name
        else if let .axiomInfo v := ci then
          if !v.isUnsafe then
            projectAxioms := projectAxioms.push name
  names := names.qsort Name.lt
  for name in names do
    logInfo m!"AUDIT_TARGET {name}"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let axioms := state.axioms.qsort Name.lt
  logInfo m!"TRANSITIVE AXIOMS: {axioms.toList}"
  logInfo m!"PROJECT LOGICAL AXIOM DECLARATIONS: {projectAxioms.toList}"
  logInfo m!"TOTAL audited theorem declarations: {names.size}"
  if names.isEmpty then
    throwError "No certificate theorems found"
  if !projectAxioms.isEmpty || axioms.any (fun a => !allowed.contains a) then
    throwError "Axiom audit failed"

