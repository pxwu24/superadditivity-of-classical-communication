import StrongConvergence.StrongConvergenceBlockCompression

/-! Axiom audit of the new deterministic reduction. The theorems which accept
joint strong convergence are conditional reductions, not unconditional proofs
of the Haar strong-convergence input. No replacement probabilistic axiom is
introduced by these files. -/

#print axioms StrongConvergenceBlock.StarPolynomial.eval_substitute
#print axioms StrongConvergenceBlock.StronglyConverges.polynomial_map
#print axioms StrongConvergenceBlock.amplify_eq_matrixUnit_polynomial
#print axioms StrongConvergenceBlock.stronglyConverges_blockModification
#print axioms StrongConvergenceBlock.tensorUnits_stronglyConverge
#print axioms StrongConvergenceBlock.shifted_compression_norm_limit
#print axioms StrongConvergenceBlock.compression_moment_limit
#print axioms StrongConvergenceBlock.amplified_compression_moment
#print axioms StrongConvergenceBlock.unamplified_compression_moment_limit
