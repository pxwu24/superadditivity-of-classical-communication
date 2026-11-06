# Block-modified strong convergence: completed proof

The original propositions and random ensembles are unchanged. The proof now establishes:

| Scope | Checked declaration | Source |
| --- | --- | --- |
| Canonical floor ranks, every k > 0 and t in (0,1) | `ProjectionChannels.Canonical.canonicalStrongInput` | [CanonicalStrong](src/StrongConvergence/StrongConvergenceCanonicalStrong.lean) |
| Arbitrary ranks and Haar projection marginals | `ProjectionChannels.HaarSequence.fullBlockModifiedStrongInput` | [HaarSequenceStrong](src/StrongConvergence/StrongConvergenceHaarSequenceStrong.lean) |
| Original random-compression proposition | `ProjectionChannels.randomCompressionStatement_verified` | [HaarPaperCorollaries](src/StrongConvergence/StrongConvergenceHaarPaperCorollaries.lean) |
| Actual finite CP/TP channel witnesses | `RevisionMain.theorem_I_1_unconditional` | [CanonicalPaperCorollaries](src/StrongConvergence/StrongConvergenceCanonicalPaperCorollaries.lean) |
| Output dimension 182 | `RevisionMatrixEntropy.exists_quantum_channels_182_unconditional` | [CanonicalPaperCorollaries](src/StrongConvergence/StrongConvergenceCanonicalPaperCorollaries.lean) |

The general theorem assumes measurable Hermitian projection matrices with the
specified Haar marginal laws and rank-density limit. It imposes no independence
assumption. The same compact probability law supplies the affine norm and weak
spectral limits, for signed real coefficient vectors and each fixed output basis.
The law is identified through both inverse-Cauchy germs, as required by the
original `IsBernoulliFreeSumLaw` definition.

## Mathematical statement


The block-modified convergence statement used by the paper is proved in Lean. It is the affine-norm and weak-spectral specialization of [Nechita, Theorem 5.2](https://arxiv.org/pdf/1802.00067).

Fix an integer $k\ge1$, $t\in(0,1)$, and integers $0\le d_n\le nk$ such that $d_n/(nk)\to t$. On a common probability space, let $P_n$ be measurable Haar-distributed orthogonal projections of rank $d_n$ on $\mathbb C^n\otimes\mathbb C^k$. No independence assumption or rate of density convergence is required. For a fixed $V\in\mathcal U(k)$ and $a\in\mathbb R^k$, write

$$
Q_n^V=(I_n\otimes V^*)P_n(I_n\otimes V)
      =\sum_{i,j=1}^k Q_{ij}^{(n,V)}\otimes E_{ij},
\qquad
S_n^V(a)=\sum_{i=1}^k a_iQ_{ii}^{(n,V)}.
$$

For $\varphi_a(X)=\mathrm{Tr}(\mathrm{diag}(a)X)I_k$, the block-modified matrix is $(\mathrm{id}_n\otimes\varphi_a)(Q_n^V)=S_n^V(a)\otimes I_k$.

Put $b_t=(1-t)\delta_0+t\delta_1$, and let $D_c$ denote dilation by $c$. There is a compactly supported probability measure

$$
\mu_{a,t}=\boxplus_{i=1}^k
              \bigl(D_{a_i/k}b_t\bigr)^{\boxplus k}
$$

such that, for every fixed $c\in\mathbb R$, almost surely,

$$
\lim_{n\to\infty} \lVert cI_n+S_n^V(a) \rVert_\infty
=\max_{x\in\mathrm{supp}\,\mu_{a,t}}|c+x|.
$$

For every fixed bounded continuous $f:\mathbb R\to\mathbb R$, almost surely,

$$
\lim_{n\to\infty}\frac1n\sum_{j=1}^n
 f\bigl(\lambda_j(S_n^V(a))\bigr)
=\int_{\mathbb R}f(x)\,d\mu_{a,t}(x).
$$

The same deterministic measure is used in both limits. In the precise Lean interface, the probability-one event may depend on the fixed choices $V,a,c$ or $V,a,f$.

The law is specified analytically, without assuming its spectral edge. Its $R$-transform is

$$
R_{\mu_{a,t}}(w)=\sum_{i=1}^k a_iR_{b_t}(a_iw/k),
\qquad
R_{b_t}(w)=
\frac{w-1+\sqrt{(1-w)^2+4tw}}{2w},
\quad R_{b_t}(0)=t.
$$

Precisely, the record requires a compact probability measure whose Cauchy transform $G(z)=\int(z-x)^{-1}\,d\mu_{a,t}(x)$ satisfies $G(z)^{-1}+R_{\mu_{a,t}}(G(z))=z$ for all sufficiently large positive $z$ and all sufficiently large negative $z$.

This is the affine-norm and weak-spectral part of the usual strong-convergence theorem; it is exactly the part required by the downstream proofs. Arbitrary noncommutative polynomial strong convergence is not the formal claim here. The formal proposition is [`ProjectionChannels.FullBlockModifiedStrongInput`](src/RandomCompression/RevisionFullBlockInput.lean). The concrete channel-existence development needs its specialization [`ProjectionChannels.Canonical.CanonicalStrongInput`](src/HaarProjections/RevisionCanonicalEnsemble.lean), where $d_n=\lfloor tkn\rfloor$; the Lean files index the positive input dimension as $n+1$.

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
| Exact Haar moments and genus estimates | [GenusExpansion](src/StrongConvergence/StrongConvergenceGenusExpansion.lean), [GenusMomentBound](src/StrongConvergence/StrongConvergenceGenusMomentBound.lean), [GenusMomentLimit](src/StrongConvergence/StrongConvergenceGenusMomentLimit.lean) |
| Concrete moment–cumulant identification | [FreeRecurrence](src/StrongConvergence/StrongConvergenceFreeRecurrence.lean), [GenusLawIdentification](src/StrongConvergence/StrongConvergenceGenusLawIdentification.lean) |
| Polynomial and smooth estimates | [GenusMaster](src/StrongConvergence/StrongConvergenceGenusMaster.lean), [SmoothMaster](src/StrongConvergence/StrongConvergenceSmoothMaster.lean), [SmoothEdge](src/StrongConvergence/StrongConvergenceSmoothEdge.lean) |
| Concentration for actual ensembles | [GaussConcentration](src/StrongConvergence/StrongConvergenceGaussConcentration.lean), [GaussGoodEvent](src/StrongConvergence/StrongConvergenceGaussGoodEvent.lean), [VariableConcentration](src/StrongConvergence/StrongConvergenceVariableConcentration.lean) |
| Arbitrary rank-density limits | [SupportDensity](src/StrongConvergence/StrongConvergenceSupportDensity.lean), [VariableSmoothEdge](src/StrongConvergence/StrongConvergenceVariableSmoothEdge.lean), [VariableStrong](src/StrongConvergence/StrongConvergenceVariableStrong.lean) |
| Arbitrary probability spaces | [HaarSequenceTransfer](src/StrongConvergence/StrongConvergenceHaarSequenceTransfer.lean), [HaarSequenceStrong](src/StrongConvergence/StrongConvergenceHaarSequenceStrong.lean) |

The [source index](verification/convergence_sources.json) records complete local import closures.
The [status record](verification/convergence_status.json) lists the final proof endpoints.

## Reproduce the checks

From the repository root, with pinned dependencies installed:

```sh
bash lean_arXiv_2607.15210/lean/verify-all.sh --no-setup --require-unconditional
```

This rebuilds every maintained Lean source, audits every declaration's
transitive axioms, checks the original public entropy statements, runs the
Python certificates, and verifies the result index and unconditional coverage.
The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

[Back to the verification summary](../readme.md)
