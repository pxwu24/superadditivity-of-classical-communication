# Partial progress: block-modified strong convergence

[All Lean sources](../lean/StrongConvergence/) · [Full unverified theorem](../README.md#remaining-unverified-block-modified-strong-convergence-theorem)

**The general theorem is not yet proved.** `CanonicalStrongInput` remains an
explicit hypothesis of the paper's random-channel theorems. None of the
results below removes that hypothesis for the output dimensions used in
the nonadditivity construction.

## Install and check

Follow the [project installation instructions](../README.md#install-and-verify),
then run from the repository root:

```sh
bash lean_arXiv_2607.15210/verify-all.sh
```

The verifier rebuilds these sources together with the existing paper proofs
and audits their transitive axioms. The recorded outputs are in
[verification/](../verification/).

## Unconditional results

| Proved result | Lean sources |
| --- | --- |
| Complete block-convergence statement for k = 1 | [Scalar case](../lean/StrongConvergence/StrongConvergenceScalar.lean) |
| Unmodified projection limits for every k > 0 | [Projection limit](../lean/StrongConvergence/StrongConvergenceScalarProjection.lean) |
| Almost-sure first compression moment, simultaneously for all real coefficient vectors | [Haar moments](../lean/StrongConvergence/StrongConvergenceHaarMoment.lean), [variance](../lean/StrongConvergence/StrongConvergenceCanonicalVariance.lean), [almost-sure limit](../lean/StrongConvergence/StrongConvergenceHaarFirstMomentAE.lean) |
| Almost-sure second compression moment for each fixed real coefficient vector | [Second moment](../lean/StrongConvergence/StrongConvergenceHaarSecondCompression.lean), [exact variance and almost-sure limit](../lean/StrongConvergence/StrongConvergenceFluctuationAE.lean) |
| Exact finite Haar entry and compression moments at every order m ≤ N, including signed coefficients | [Haar integration](../lean/StrongConvergence/StrongConvergenceTensorWeingarten.lean), [compression cycles](../lean/StrongConvergence/StrongConvergenceTensorCompressionCycles.lean), [canonical sequence](../lean/StrongConvergence/StrongConvergenceTensorCanonical.lean) |
| Exact Gram row formula and quantitative inverse-Gram bound | [Gram row](../lean/StrongConvergence/StrongConvergenceTensorGramRow.lean), [inverse bound](../lean/StrongConvergence/StrongConvergenceTensorInverseBound.lean) |
| Arbitrary-order inverse-Gram expansion and vanishing-error approximation to every fixed expected compression moment | [Inverse asymptotics](../lean/StrongConvergence/StrongConvergenceTensorInverseAsymptotics.lean), [actual Haar moment approximation](../lean/StrongConvergence/StrongConvergenceTensorMomentAsymptotics.lean) |
| Deterministic signed spectral enclosure and affine norm envelope | [Spectral enclosure](../lean/StrongConvergence/StrongConvergenceSpectralEstimate.lean) |
| Matrix-unit strong limit and deterministic compression norm bound | [Matrix units](../lean/StrongConvergence/StrongConvergenceBlockMatrixUnits.lean), [norm bound](../lean/StrongConvergence/StrongConvergenceCompressionBounds.lean) |
| Counterexample: fixed moments and weak spectral convergence alone do not imply norm convergence | [Spectral outlier example](../lean/StrongConvergence/StrongConvergenceOutlier.lean) |

The unmodified projection limits hold for every unitary sample. The first
Haar compression moment also converges almost surely, on one event for every a:

```math
\frac{1}{n}\mathrm{Tr}\,S_n(a)
\longrightarrow t\sum_i a_i\qquad\text{almost surely}.
```

The proof derives Haar quadratic moments from permutation invariance and
explicit two-coordinate real and imaginary unitary rotations. For the
normalized trace q_n, it proves the actual estimate

```math
\mathbb{E}\bigl[(q_n-\mathbb{E} q_n)^2\bigr]
\leq\frac{\sum_i a_i^2}{k n^2}
```

and applies Borel–Cantelli. Lean indexes the positive input dimension by n+1.

The exact finite Haar calculation also proves

```math
\frac{1}{n}\mathbb{E}\mathrm{Tr}(S_n(a)^2)
\longrightarrow
t^2\left(\sum_i a_i\right)^2+
\frac{t(1-t)}{k}\sum_i a_i^2.
```

The second moment also converges almost surely for each fixed signed real
coefficient vector in the canonical ensemble, for k >= 2 and t in [0,1]:

```math
\frac1n\mathrm{Tr}(S_n(a)^2)
\longrightarrow
t^2\left(\sum_i a_i\right)^2+
\frac{t(1-t)}k\sum_i a_i^2
\qquad\text{almost surely}.
```

This conclusion is proved from the actual Haar measure. The proof evaluates
all fourth-order permutation contractions, computes the variance of the
normalized second trace exactly, and establishes an eventual bound C/n^2.
Borel–Cantelli then gives the displayed almost-sure limit. No concentration
or strong-convergence assertion is assumed. This result concerns the second
moment; it does not establish convergence of every moment or exclude outliers.

| Second-moment proof step | Lean sources |
| --- | --- |
| Kernel-checked finite permutation counts and exact inverse-Gram coefficients | [Finite certificates](../lean/StrongConvergence/StrongConvergenceFourthFinite.lean), [fourth coefficients](../lean/StrongConvergence/StrongConvergenceFourthCoefficients.lean) |
| Haar two-trace integral and conjugacy-class weights | [Moment contractions](../lean/StrongConvergence/StrongConvergenceFluctuationMoments.lean), [weights](../lean/StrongConvergence/StrongConvergenceFluctuationWeights.lean), [finite classes](../lean/StrongConvergence/StrongConvergenceFluctuationFinite.lean), [class reduction](../lean/StrongConvergence/StrongConvergenceFluctuationClasses.lean) |
| Exact rational variance and its summable asymptotic bound | [Normalization](../lean/StrongConvergence/StrongConvergenceFourthNormalization.lean), [variance asymptotics](../lean/StrongConvergence/StrongConvergenceSecondVarianceAsymptotics.lean) |
| Actual canonical variance and almost-sure conclusion | [Integrability and centering](../lean/StrongConvergence/StrongConvergenceFluctuationAEBase.lean), [Haar second-moment limit](../lean/StrongConvergence/StrongConvergenceFluctuationAE.lean) |

The k = 1 result includes signed coefficients, arbitrary scalar shifts,
output-unitary rotations, and bounded continuous test functions. The paper
needs k >= 2, where the compression is no longer a scalar multiple of the
original projection.

## All-order finite Haar integration

The finite integration formula is proved from Haar invariance, rather than
assumed as an additional input. Write N = nk and let P be a rank-d orthogonal
projection on C^n tensor C^k. For a real coefficient vector a and Haar U, put
S = sum_i a_i (UPU*)_ii. For every 1 <= m <= N, the checked formula is

```math
\mathbb{E}\mathrm{Tr}(S^m)
=\sum_{\sigma\in S_m}c_\sigma\,
  n^{\#\mathrm{cycles}(\gamma\sigma)}
  \prod_{C\in\mathrm{cycles}(\sigma)}\sum_{i=1}^k a_i^{|C|},
\qquad \gamma=(1\;2\;\cdots\;m),
```

where the coefficients are entirely finite and deterministic:

```math
G_{\sigma,\tau}=N^{\#\mathrm{cycles}(\tau\sigma^{-1})},
\qquad
c=G^{-1}\bigl(d^{\#\mathrm{cycles}(\tau^{-1})}\bigr)_{\tau\in S_m}.
```

The same identity is proved for the actual `Canonical.probability` and its
floor-rank sequence. The canonical theorem indexes the power by m+1 and the
input dimension by n+1; its eventual version constructs the required
dimension embedding internally. Signed coefficients are included.

The complete proof chain is:

| Step | Related Lean files |
| --- | --- |
| Tensor powers and diagonal phase invariance | [Power](../lean/StrongConvergence/StrongConvergenceTensorPower.lean), [Phase](../lean/StrongConvergence/StrongConvergenceTensorPhase.lean) |
| Unitary commutation extends to all complex matrices; invariant tensors are spanned by permutations | [Complexification](../lean/StrongConvergence/StrongConvergenceTensorComplexification.lean), [Spanning](../lean/StrongConvergence/StrongConvergenceTensorSpanning.lean) |
| Actual Haar average is invariant; its contractions are preserved | [Haar integral](../lean/StrongConvergence/StrongConvergenceTensorHaarIntegral.lean), [Haar trace](../lean/StrongConvergence/StrongConvergenceTensorHaarTrace.lean) |
| Permutation operators, cycle counts, and invertible Gram matrix | [Permutation](../lean/StrongConvergence/StrongConvergenceTensorPermutation.lean), [Cycles](../lean/StrongConvergence/StrongConvergenceTensorCycles.lean), [Gram](../lean/StrongConvergence/StrongConvergenceTensorGram.lean) |
| Projection contractions and all-order integration | [Projection](../lean/StrongConvergence/StrongConvergenceTensorProjection.lean), [Weingarten](../lean/StrongConvergence/StrongConvergenceTensorWeingarten.lean) |
| Compression expansion, cycle formula, and canonical specialization | [Block moments](../lean/StrongConvergence/StrongConvergenceTensorBlockMoments.lean), [Compression cycles](../lean/StrongConvergence/StrongConvergenceTensorCompressionCycles.lean), [Weighted cycles](../lean/StrongConvergence/StrongConvergenceTensorWeightedCycles.lean), [Canonical](../lean/StrongConvergence/StrongConvergenceTensorCanonical.lean) |
| Quantitative bounds, including a Burnside orbit-count calculation | [Gram bounds](../lean/StrongConvergence/StrongConvergenceTensorGramBounds.lean), [Gram row](../lean/StrongConvergence/StrongConvergenceTensorGramRow.lean), [Inverse bound](../lean/StrongConvergence/StrongConvergenceTensorInverseBound.lean) |

In the maximum absolute row-sum norm, these files prove the exact identity
and inverse estimate

```math
\|N^{-m}G-I\|_{\mathrm{row}}
=\varepsilon_{N,m}:=\prod_{j=0}^{m-1}(1+j/N)-1,
\qquad
\|N^mG^{-1}-I\|_{\mathrm{row}}
\le\frac{\varepsilon_{N,m}}{1-\varepsilon_{N,m}}
\quad(\varepsilon_{N,m}<1).
```

These are bounds for a finite permutation Gram matrix. They are not sharp
spectral bounds for the random compression.

The inverse approximation now has arbitrary fixed-order precision. Put
C_m = m! - 1. For fixed m >= 1 and r >= 0, and N > C_m, the checked row bound is

```math
N^r\sum_\tau\left|
N^m(G_N^{-1})_{\sigma,\tau}
-\left[\sum_{\ell=0}^{r}(I-N^{-m}G_N)^\ell\right]_{\sigma,\tau}
\right|
\leq\frac{C_m^{r+1}}{N-C_m}.
```

The right side tends to zero. The bound is transferred to the actual Haar
projection coefficients, for any rank sequence within the ambient dimensions.
For a trace moment of fixed order m, taking m+1 Neumann terms also gives a
finite inverse-free approximation to the canonical expected trace with
vanishing absolute error, even before normalized-trace division. The exported
theorem is `Canonical.integral_compression_trace_neumann_approximation`.
Identifying the limit of the resulting finite permutation expression still
requires the geodesic/noncrossing cancellations and the free-law calculation.


The standard-library Python implementation uses exact rational arithmetic:

```sh
python3 lean_arXiv_2607.15210/partial_progress/exact_haar_moments.py
```

[The program](exact_haar_moments.py) checks the first two known moments,
zero/full-rank and rank-one projections through order four, and the Gram
and inverse-Gram bounds. Its matrix has m! rows, so it is intended for small
orders. These finite checks do not certify asymptotic strong convergence.

## Proved reductions with explicit hypotheses

These are intermediate theorems. Their hypotheses still need to be proved
for Haar block compressions before the general result becomes unconditional.

| Step | What is proved | Entry files |
| --- | --- | --- |
| Block modification | Every square complex-linear block map is a fixed matrix-unit sandwich polynomial; polynomial substitution preserves joint strong convergence. | [Polynomials](../lean/StrongConvergence/StrongConvergenceBlockPolynomials.lean), [Modification](../lean/StrongConvergence/StrongConvergenceBlockModification.lean), [Compression](../lean/StrongConvergence/StrongConvergenceBlockCompression.lean) |
| Moments to weak convergence | Common compact support and convergence of all normalized trace moments give actual continuous spectral-test convergence. A countable moment event suffices for all continuous tests. | [Moments](../lean/StrongConvergence/StrongConvergenceMoments.lean), [Empirical measures](../lean/StrongConvergence/StrongConvergenceMomentMeasures.lean), [Matrices](../lean/StrongConvergence/StrongConvergenceMomentMatrices.lean) |
| Almost-sure convergence | Summable deviation probabilities or second-moment bounds give simultaneous convergence for countably many tests; Lipschitz continuity extends this to all parameters and uniformly over compact parameter sets. | [Probability](../lean/StrongConvergence/StrongConvergenceProbability.lean), [Second moments](../lean/StrongConvergence/StrongConvergenceProbabilityMoments.lean), [Dense parameters](../lean/StrongConvergence/StrongConvergenceProbabilityDense.lean) |
| Lower norm bound | Weak spectral convergence forces the eventual norm to exceed every smaller value than the limiting support norm. | [Lower bound](../lean/StrongConvergence/StrongConvergenceNormLower.lean) |
| Upper norm bound | Markov's inequality and Borel–Cantelli turn summable expected high-even-trace ratios into almost-sure upper norm bounds. | [Finite norm bound](../lean/StrongConvergence/StrongConvergenceNorm.lean), [Random matrices](../lean/StrongConvergence/StrongConvergenceNormProbability.lean) |
| Norm and spectral-test assembly | Actual normalized trace-moment convergence and summable expected high-even-trace estimates imply both norm convergence to the support norm and all continuous spectral-test limits, on one probability-one event. | [Assembly](../lean/StrongConvergence/StrongConvergenceMomentStrong.lean) |

The assembly theorem concerns the norm of the matrix itself. To obtain the
standard strong-convergence conclusion for every polynomial, its hypotheses
must also be established for those polynomials.

The last step uses the finite-matrix inequality

```math
\mathbb{P}\{\|M_n\|\ge R\}
\le R^{-2q_n}\mathbb{E}\mathrm{Tr}(M_n^{2q_n}),
```

with a moment order allowed to grow with dimension. Establishing a summable
right-hand side for every R above the proposed limiting norm is the remaining
upper-edge problem. Merely knowing each fixed-order moment limit is insufficient:
the formalized example `diag(2,0,...,0)` has limiting empirical law delta_0
while its operator norm is always 2.

## Remaining mathematical work

1. Extract the all-order limiting moments from the finite permutation formula
   and identify the compression's inverse-Cauchy germ with the Bernoulli
   free-sum germ used by `IsBernoulliFreeSumLaw`. Arbitrary-order inverse-Gram precision and its transfer to actual expected
   compression moments are now proved. The remaining identification requires
   evaluating the finite expressions through geodesic/noncrossing permutation
   cancellations. The moment-based route also needs summable fluctuation
   estimates beyond the first and second moments to pass to almost-sure
   weak convergence.
2. Prove sharp high-degree moment estimates or resolvent estimates that exclude
   eigenvalues outside the limiting support. The probability and norm lemmas
   above make the required quantitative implication explicit, but do not
   establish those Haar estimates.
3. Combine those results to prove the existing `FullBlockModifiedStrongInput`
   for every required k and t, then remove the input parameter from the paper
   theorems and rerun the complete audit.

An alternative route is to formalize Haar joint strong asymptotic freeness
and free compression. The published block-modification proof uses those
substantial results; polynomial closure alone is not a proof of the random
theorem. When applying joint strong freeness through a reference projection,
joint convergence with the tensor matrix units also needs justification.

## Primary references

- [Nechita, Section 5, Theorem 5.2](https://arxiv.org/html/1802.00067v2#S5):
  block modification by a fixed polynomial and its distributional input.
- [Collins–Male, Theorem 1.4](https://arxiv.org/pdf/1105.4345): joint strong
  asymptotic freeness of Haar matrices and an independent strongly convergent
  family.
- [Arizmendi–Nechita–Vargas, Section 2.4 and Theorem 5.1](https://arxiv.org/pdf/1508.05732):
  corner-block cumulants and the limiting block-modification law.
- [Collins–Śniady, Haar integration](https://arxiv.org/abs/math-ph/0402073):
  finite Haar moment formulas underlying a possible direct approach.

The [source index](source_index.json) lists all new Lean modules and their
complete local import closures. The [status record](status.json) records
which convergence assertions remain open.

The main [project citation](../README.md#citation) points to the checked source
snapshot. Successful compilation of the reductions above must not be reported
as unconditional verification of the general random-matrix theorem.
