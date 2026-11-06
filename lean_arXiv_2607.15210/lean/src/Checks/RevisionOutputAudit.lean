import OutputStates.RevisionOutputHausdorff

/-! Kernel dependency audit for Theorem III.1 and Lemmas III.3--III.4.
The strong-convergence input in Theorem III.1 is an explicit theorem
parameter, not an added axiom. -/

#print axioms RevisionOutput.output_space_limit
#print axioms RevisionOutput.output_space_metric_limit
#print axioms RevisionOutput.traceHausdorff_eq_matrixSupportDistance
#print axioms RevisionOutput.local_channel_support_threshold
#print axioms RevisionOutput.normalized_output_support
#print axioms RevisionOutput.ae_eventually_marginal_posDef
#print axioms RevisionOutput.isCompact_spectralBody
#print axioms RevisionOutput.convex_spectralBody
#print axioms RevisionOutput.spectralBody_support
