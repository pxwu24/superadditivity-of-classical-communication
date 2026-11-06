# Block-modified strong convergence: completed proof

The original propositions and random ensembles are unchanged. The proof now establishes:

| Scope | Checked declaration | Source |
| --- | --- | --- |
| Canonical floor ranks, every k > 0 and t in (0,1) | `ProjectionChannels.Canonical.canonicalStrongInput` | [CanonicalStrong](../lean/StrongConvergence/StrongConvergenceCanonicalStrong.lean) |
| Arbitrary ranks and Haar projection marginals | `ProjectionChannels.HaarSequence.fullBlockModifiedStrongInput` | [HaarSequenceStrong](../lean/StrongConvergence/StrongConvergenceHaarSequenceStrong.lean) |
| Original random-compression proposition | `ProjectionChannels.randomCompressionStatement_verified` | [HaarPaperCorollaries](../lean/StrongConvergence/StrongConvergenceHaarPaperCorollaries.lean) |
| Actual finite CP/TP channel witnesses | `RevisionMain.theorem_I_1_unconditional` | [CanonicalPaperCorollaries](../lean/StrongConvergence/StrongConvergenceCanonicalPaperCorollaries.lean) |
| Output dimension 182 | `RevisionMatrixEntropy.exists_quantum_channels_182_unconditional` | [CanonicalPaperCorollaries](../lean/StrongConvergence/StrongConvergenceCanonicalPaperCorollaries.lean) |

The general theorem assumes measurable Hermitian projection matrices with the
specified Haar marginal laws and rank-density limit. It imposes no independence
assumption. The same compact probability law supplies the affine norm and weak
spectral limits, for signed real coefficient vectors and each fixed output basis.
The law is identified through both inverse-Cauchy germs, as required by the
original `IsBernoulliFreeSumLaw` definition.

## Why the proof works

For one output block, the compression is a scalar multiple of a projection.
Its spectrum lies in {0,a}, and an interior limiting rank density makes both
spectral values occur eventually. The weak and affine norm limits follow from
these two eigenvalues and their multiplicities.

With several output blocks, the diagonal blocks are no longer projections.
The proof first determines their limiting moments. This alone cannot control
the norm: a single isolated eigenvalue has vanishing empirical mass. The
remaining argument therefore controls smooth tests supported above the
limiting spectral edge, then upgrades those estimates to almost-sure bounds.

1. **Identify the bulk law.** Exact Haar integration gives a permutation
   expansion of every trace moment. Permutation length and parity organize
   the expansion by genus. The leading terms satisfy the concrete marked-cycle
   moment–cumulant recursion. This identifies the compact limiting measure
   with the Bernoulli free-sum law, including its actual inverse-Cauchy germs.
2. **Exclude outliers.** A degree-uniform polynomial estimate extends to
   smooth spectral tests through a rapidly decaying Chebyshev expansion. For
   fixed density, positivity cancels the first-order density error. For
   arbitrary rank sequences, upper semicontinuity of the explicit support
   function makes the leading smooth test vanish at all nearby densities.
   The expected normalized test is O(N^-2), so its unnormalized trace tends
   to zero and the outlier probability vanishes.
3. **Obtain almost-sure limits.** Gaussian concentration, conditioning bounds,
   and whitening give summable centered tails for the actual Haar ensemble.
   These yield almost-sure moment limits and upgrade the vanishing outlier
   probabilities to almost-sure edge bounds. Weak convergence supplies the
   matching lower norm bound at the support endpoints.
4. **Transfer the statement.** Fixed output rotations preserve Haar measure.
   Equal-rank projections have the same Haar orbit law. Summable coordinate
   tails transfer the result to arbitrary joint couplings with the required
   Haar marginals, including the independent sequence in the paper.

All ingredients above are formal theorems. Numerical checks are not used as
substitutes for the universal moment, concentration, or outlier estimates.

## Proof entry points

| Ingredient | Modules |
| --- | --- |
| Exact Haar moments and genus estimates | [GenusExpansion](../lean/StrongConvergence/StrongConvergenceGenusExpansion.lean), [GenusMomentBound](../lean/StrongConvergence/StrongConvergenceGenusMomentBound.lean), [GenusMomentLimit](../lean/StrongConvergence/StrongConvergenceGenusMomentLimit.lean) |
| Concrete moment–cumulant identification | [FreeRecurrence](../lean/StrongConvergence/StrongConvergenceFreeRecurrence.lean), [GenusLawIdentification](../lean/StrongConvergence/StrongConvergenceGenusLawIdentification.lean) |
| Polynomial and smooth estimates | [GenusMaster](../lean/StrongConvergence/StrongConvergenceGenusMaster.lean), [SmoothMaster](../lean/StrongConvergence/StrongConvergenceSmoothMaster.lean), [SmoothEdge](../lean/StrongConvergence/StrongConvergenceSmoothEdge.lean) |
| Concentration for actual ensembles | [GaussConcentration](../lean/StrongConvergence/StrongConvergenceGaussConcentration.lean), [GaussGoodEvent](../lean/StrongConvergence/StrongConvergenceGaussGoodEvent.lean), [VariableConcentration](../lean/StrongConvergence/StrongConvergenceVariableConcentration.lean) |
| Arbitrary rank-density limits | [SupportDensity](../lean/StrongConvergence/StrongConvergenceSupportDensity.lean), [VariableSmoothEdge](../lean/StrongConvergence/StrongConvergenceVariableSmoothEdge.lean), [VariableStrong](../lean/StrongConvergence/StrongConvergenceVariableStrong.lean) |
| Arbitrary probability spaces | [HaarSequenceTransfer](../lean/StrongConvergence/StrongConvergenceHaarSequenceTransfer.lean), [HaarSequenceStrong](../lean/StrongConvergence/StrongConvergenceHaarSequenceStrong.lean) |

The [source index](source_index.json) records complete local import closures.
The [status record](status.json) lists the final proof endpoints.

## Reproduce the checks

From the repository root, with pinned dependencies installed:

```sh
bash lean_arXiv_2607.15210/verify-all.sh --no-setup --require-unconditional
```

This rebuilds every maintained Lean source, audits every declaration's
transitive axioms, checks the original public entropy statements, runs the
Python certificates, and verifies the result index and unconditional coverage.
The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The full mathematical statement is in the [main README](../README.md#verified-block-modified-strong-convergence-theorem).
The [original blueprint progress note](blueprint_progress_20261105.md) is retained
as a dated historical checkpoint.
