import Preliminaries.PaperFormalization
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0

/- Check all project theorem declarations, including generated and private
helpers, with Lean's standard transitive axiom collector. Shared visitation
avoids repeatedly traversing identical mathlib dependency subgraphs. -/
open Lean in
run_elab do
  let projectModules : Array Name := #[`Preliminaries.PreliminariesMatrix, `Preliminaries.PreliminariesChoi, `Preliminaries.PreliminariesLegendre, `Preliminaries.PreliminariesAnalysis, `Preliminaries.CompletePositivity, `RandomCompression.BernoulliCalculus, `RandomCompression.BernoulliDuality, `RandomCompression.BernoulliEdgeCalculus, `RandomCompression.BernoulliCriticalPoint, `RandomCompression.CompressionSpectral, `RandomCompression.CompressionExtension, `RandomCompression.BlockModification, `RandomCompression.ProjectionStrongConvergence, `HaarProjections.GaussianRank, `HaarProjections.GaussianRadial, `HaarProjections.GaussianUnitary, `HaarProjections.GaussianMatrixLaw, `HaarProjections.HaarProjection, `HaarProjections.HaarMeasure, `HaarProjections.HaarOrbitUnique, `HaarProjections.GaussianWhitening, `HaarProjections.ProjectionOrbit, `HaarProjections.MatrixRankMeasurable, `HaarProjections.HaarLocalSupport, `HaarProjections.HaarFullLocalSupport, `RandomCompression.CauchyBernoulli, `RandomCompression.CauchyHolomorphic, `RandomCompression.SpectralEdge, `RandomCompression.CauchyHolomorphy, `RandomCompression.CauchyLocalInverse]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut projectAxioms : Array Name := #[]
  let mut compilerArtifacts : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if let some mi := env.getModuleIdxFor? name then
      if projectModules.contains env.allImportedModuleNames[mi.toNat]! then
        if ci.isTheorem then
          names := names.push name
        else if let .axiomInfo v := ci then
          if v.isUnsafe then
            compilerArtifacts := compilerArtifacts.push name
          else
            projectAxioms := projectAxioms.push name
  names := names.qsort Name.lt
  for name in names do
    logInfo m!"AUDIT_TARGET {name}"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let axioms := state.axioms.qsort Name.lt
  logInfo m!"TRANSITIVE AXIOMS: {axioms.toList}"
  logInfo m!"PROJECT LOGICAL AXIOM DECLARATIONS: {projectAxioms.toList}"
  logInfo m!"UNSAFE COMPILER ARTIFACTS (not proof dependencies): {compilerArtifacts.toList}"
  logInfo m!"TOTAL audited theorem declarations: {names.size}"
  if !projectAxioms.isEmpty || axioms.any (fun a => !allowed.contains a) then
    throwError "Axiom audit failed"

