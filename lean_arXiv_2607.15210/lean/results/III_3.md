# Lemma III.3: Support-function formula for trace-norm Hausdorff distance

Complete.

Exact trace-norm Hausdorff distance equals the supremum of support-function differences over the Hermitian operator-norm unit ball. Trace/operator duality is attained by explicit spectral witnesses; compact trace balls and the separation argument are proved.

## Check this result

First run `bash lean_arXiv_2607.15210/lean/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/lean/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionOutput.traceHausdorff_eq_matrixSupportDistance
#print axioms RevisionOutput.traceHausdorff_eq_matrixSupportDistance
#check RevisionOutput.trace_operator_duality_named
#print axioms RevisionOutput.trace_operator_duality_named
#check RevisionOutput.density_opNorm_witness
#print axioms RevisionOutput.density_opNorm_witness
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. The entry declarations include the completed paper endpoints.

## Entry files

- [OutputStates.RevisionOutputHausdorff](../src/OutputStates/RevisionOutputHausdorff.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [src/BellOutput/RevisionBellContraction.lean](../src/BellOutput/RevisionBellContraction.lean)
- [src/Entropy/Analysis.lean](../src/Entropy/Analysis.lean)
- [src/Entropy/Combinatorics.lean](../src/Entropy/Combinatorics.lean)
- [src/Entropy/Defs.lean](../src/Entropy/Defs.lean)
- [src/Entropy/Infimum.lean](../src/Entropy/Infimum.lean)
- [src/Entropy/Localization.lean](../src/Entropy/Localization.lean)
- [src/Entropy/Minimum.lean](../src/Entropy/Minimum.lean)
- [src/Entropy/OutputSpace.lean](../src/Entropy/OutputSpace.lean)
- [src/Entropy/OutputSpaceBody.lean](../src/Entropy/OutputSpaceBody.lean)
- [src/Entropy/Single.lean](../src/Entropy/Single.lean)
- [src/Entropy/Spike.lean](../src/Entropy/Spike.lean)
- [src/Entropy/SpikeArithmetic.lean](../src/Entropy/SpikeArithmetic.lean)
- [src/HaarProjections/HaarMeasure.lean](../src/HaarProjections/HaarMeasure.lean)
- [src/HaarProjections/HaarProjection.lean](../src/HaarProjections/HaarProjection.lean)
- [src/OutputStates/OutputSpaceCompressionBridge.lean](../src/OutputStates/OutputSpaceCompressionBridge.lean)
- [src/OutputStates/OutputSpaceMatrix.lean](../src/OutputStates/OutputSpaceMatrix.lean)
- [src/OutputStates/RevisionOutputBody.lean](../src/OutputStates/RevisionOutputBody.lean)
- [src/OutputStates/RevisionOutputChannel.lean](../src/OutputStates/RevisionOutputChannel.lean)
- [src/OutputStates/RevisionOutputConvergence.lean](../src/OutputStates/RevisionOutputConvergence.lean)
- [src/OutputStates/RevisionOutputDuality.lean](../src/OutputStates/RevisionOutputDuality.lean)
- [src/OutputStates/RevisionOutputEventual.lean](../src/OutputStates/RevisionOutputEventual.lean)
- [src/OutputStates/RevisionOutputFunctionals.lean](../src/OutputStates/RevisionOutputFunctionals.lean)
- [src/OutputStates/RevisionOutputGeometry.lean](../src/OutputStates/RevisionOutputGeometry.lean)
- [src/OutputStates/RevisionOutputHausdorff.lean](../src/OutputStates/RevisionOutputHausdorff.lean)
- [src/OutputStates/RevisionOutputLimit.lean](../src/OutputStates/RevisionOutputLimit.lean)
- [src/OutputStates/RevisionOutputMetricComparison.lean](../src/OutputStates/RevisionOutputMetricComparison.lean)
- [src/OutputStates/RevisionOutputProbability.lean](../src/OutputStates/RevisionOutputProbability.lean)
- [src/OutputStates/RevisionOutputStates.lean](../src/OutputStates/RevisionOutputStates.lean)
- [src/OutputStates/RevisionOutputTheorem.lean](../src/OutputStates/RevisionOutputTheorem.lean)
- [src/OutputStates/RevisionOutputTraceBalls.lean](../src/OutputStates/RevisionOutputTraceBalls.lean)
- [src/OutputStates/RevisionOutputTraceDistance.lean](../src/OutputStates/RevisionOutputTraceDistance.lean)
- [src/OutputStates/RevisionOutputTraceGeometry.lean](../src/OutputStates/RevisionOutputTraceGeometry.lean)
- [src/OutputStates/RevisionOutputUnitary.lean](../src/OutputStates/RevisionOutputUnitary.lean)
- [src/Preliminaries/CompletePositivity.lean](../src/Preliminaries/CompletePositivity.lean)
- [src/Preliminaries/PreliminariesAnalysis.lean](../src/Preliminaries/PreliminariesAnalysis.lean)
- [src/Preliminaries/PreliminariesChoi.lean](../src/Preliminaries/PreliminariesChoi.lean)
- [src/Preliminaries/PreliminariesLegendre.lean](../src/Preliminaries/PreliminariesLegendre.lean)
- [src/Preliminaries/PreliminariesMatrix.lean](../src/Preliminaries/PreliminariesMatrix.lean)
- [src/Preliminaries/RevisionTraceDuality.lean](../src/Preliminaries/RevisionTraceDuality.lean)
- [src/RandomCompression/BernoulliCalculus.lean](../src/RandomCompression/BernoulliCalculus.lean)
- [src/RandomCompression/BernoulliCriticalPoint.lean](../src/RandomCompression/BernoulliCriticalPoint.lean)
- [src/RandomCompression/BernoulliDuality.lean](../src/RandomCompression/BernoulliDuality.lean)
- [src/RandomCompression/BernoulliEdgeCalculus.lean](../src/RandomCompression/BernoulliEdgeCalculus.lean)
- [src/RandomCompression/BlockModification.lean](../src/RandomCompression/BlockModification.lean)
- [src/RandomCompression/CauchyBernoulli.lean](../src/RandomCompression/CauchyBernoulli.lean)
- [src/RandomCompression/CauchyHolomorphic.lean](../src/RandomCompression/CauchyHolomorphic.lean)
- [src/RandomCompression/CauchyHolomorphy.lean](../src/RandomCompression/CauchyHolomorphy.lean)
- [src/RandomCompression/CauchyLocalInverse.lean](../src/RandomCompression/CauchyLocalInverse.lean)
- [src/RandomCompression/CompressionEndpointGlue.lean](../src/RandomCompression/CompressionEndpointGlue.lean)
- [src/RandomCompression/CompressionExtension.lean](../src/RandomCompression/CompressionExtension.lean)
- [src/RandomCompression/CompressionSpectral.lean](../src/RandomCompression/CompressionSpectral.lean)
- [src/RandomCompression/ProjectionStrongConvergence.lean](../src/RandomCompression/ProjectionStrongConvergence.lean)
- [src/RandomCompression/RevisionBernoulliCauchy.lean](../src/RandomCompression/RevisionBernoulliCauchy.lean)
- [src/RandomCompression/RevisionBernoulliCompression.lean](../src/RandomCompression/RevisionBernoulliCompression.lean)
- [src/RandomCompression/RevisionBernoulliEdge.lean](../src/RandomCompression/RevisionBernoulliEdge.lean)
- [src/RandomCompression/RevisionBernoulliHolomorphic.lean](../src/RandomCompression/RevisionBernoulliHolomorphic.lean)
- [src/RandomCompression/RevisionBernoulliLaw.lean](../src/RandomCompression/RevisionBernoulliLaw.lean)
- [src/RandomCompression/RevisionBernoulliTensor.lean](../src/RandomCompression/RevisionBernoulliTensor.lean)
- [src/RandomCompression/RevisionFullBlockInput.lean](../src/RandomCompression/RevisionFullBlockInput.lean)
- [src/RandomCompression/SpectralEdge.lean](../src/RandomCompression/SpectralEdge.lean)

## Assumptions and dependencies

- Nonempty compact convex sets C,K of Hermitian k-by-k matrices. The PDF omits nonemptiness and should add it.
