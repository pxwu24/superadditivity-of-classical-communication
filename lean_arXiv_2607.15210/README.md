# Lean verification for arXiv:2607.15210

Proof sources and numerical certificates for *Counterexamples to additivity of
minimum output p-Rényi entropy of quantum channels for all p ≥ 0*.

**Verification summary.** The finite-dimensional, analytic, entropy, and
dimension-182 spectral estimates have Lean proofs. The random-channel limits
and channel-existence conclusions have Lean proofs **assuming one remaining
theorem: block-modified strong convergence for bipartite Haar projections**.
Its full statement appears below. 

The remaining work is mathematical: identifying the limiting free law and proving sharp estimates that exclude spectral outliers. The verified progress toward that theorem is recorded below.

Every result in the tables links to its declarations, assumptions, and **all
related Lean files**. Proof sources are grouped by topic in [lean/](lean/);
[Python checks](python/) and [verification records](verification/) have separate folders.

## Install and verify

Install Git, Bash, Python 3.11 or newer with `venv`, and Lean's toolchain manager
[elan](https://github.com/leanprover/elan#installation). On Windows, use WSL.

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
# Open a new terminal after installation, then:
git clone https://github.com/pxwu24/superadditivity-of-classical-communication.git
cd superadditivity-of-classical-communication
bash lean_arXiv_2607.15210/verify-all.sh
```

The project selects Lean **4.19.0** and the pinned Mathlib dependency
automatically. To recheck an existing installation:

```sh
bash lean_arXiv_2607.15210/verify-all.sh --no-setup
```

This rebuilds every maintained Lean source, audits all declarations, and runs
the Python checks. Only the standard Lean axioms `propext`, `Classical.choice`,
and `Quot.sound` are allowed. A successful build checks the stated hypotheses;
it does not prove the remaining convergence theorem.

## Results fully verified

<!-- RESULT_TABLE_START -->
| Paper result | Verified statement |
| --- | --- |
| [Lemma II.2](results/II_2.md) | Full local support of a Haar-random subspace |
| [Lemma A.1](results/A_1.md) | Bernoulli free-convolution spectral edge |
| [Lemma III.3](results/III_3.md) | Support-function formula for trace-norm Hausdorff distance |
| [Lemma III.4](results/III_4.md) | Channel support and generalized-eigenvalue threshold |
| [Lemma A.2](results/A_2.md) | Second logarithmic variation |
| [Proposition V.2](results/V_2.md) | Eigenvalue shuffling |
| [Proposition B.1](results/B_1.md) | Entropy of the one-channel output body after antisymmetric postprocessing |
| [Proposition B.2](results/B_2.md) | Entropy of the limiting Bell output after antisymmetric postprocessing |
| [Proposition VI.1](results/VI_1.md) | Dimension-182 spectral/body certificate (exact entropy gap) |
| [Lemma C.1](results/C_1.md) | Reduction of the entropy minimum |
| [Lemma C.2](results/C_2.md) | Scalar certificate for the largest eigenvalue |
<!-- RESULT_TABLE_END -->

The dimension-182 certificate proves the strict limiting spectral inequality.
The finite-channel consequence uses the convergence theorem below, and the
bound is **k_high(1) ≤ 182**.

## Results verified conditioned on block-modified strong convergence theorem

The following proofs are complete if we assume the block-modified strong convergence theorem.

<!-- CONDITIONAL_TABLE_START -->
| Paper result | Verified statement |
| --- | --- |
| [Lemma II.3](results/II_3.md) | Random compression formula |
| [Theorem III.1](results/III_1.md) | Hausdorff limit of output state spaces |
| [Corollary III.2](results/III_2.md) | One-copy entropy limit and asymptotics |
| [Theorem IV.1](results/IV_1.md) | Limit of the Bell output |
| [Corollary IV.2](results/IV_2.md) | Product-channel bound and Bell entropy expansion |
| [Proposition A.3](results/A_3.md) | Second moments after local normalization |
| [Proposition A.4](results/A_4.md) | Asymptotic second Choi moment |
| [Theorem V.1](results/V_1.md) | Single-output and Bell-output asymptotics after antisymmetric postprocessing |
| [Theorem I.1](results/I_1.md) | Nonadditivity for every positive Renyi order |
| [Proposition VI.1](results/VI_1.md) | Dimension-182 finite-channel consequence of the certified gap |
<!-- CONDITIONAL_TABLE_END -->

## Remaining unverified block-modified strong convergence theorem

The remaining unverified result is **block-modified strong convergence for Haar projections, for fixed output dimension $k\ge2$**. It is Theorem 5.2 in https://arxiv.org/pdf/1802.00067. The precise statement used in the paper is the following.

Fix $k\ge2$, $t\in(0,1)$, and integers $0\le d_n\le nk$ such that $d_n/(nk)\to t$. Let $P_n$ be independent Haar-distributed orthogonal projections of rank $d_n$ on $\mathbb C^n\otimes\mathbb C^k$. For a fixed $V\in\mathcal U(k)$ and $a\in\mathbb R^k$, write

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
\lim_{n\to\infty} || cI_n+S_n^V(a) ||_\infty
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

This is the affine-norm and weak-spectral part of the usual strong-convergence theorem; it is exactly the part required by the downstream proofs. The formal proposition is [`ProjectionChannels.FullBlockModifiedStrongInput`](lean/RandomCompression/RevisionFullBlockInput.lean). The concrete channel-existence development needs its specialization [`ProjectionChannels.Canonical.CanonicalStrongInput`](lean/HaarProjections/RevisionCanonicalEnsemble.lean), where $d_n=\lfloor tkn\rfloor$; the Lean files index the positive input dimension as $n+1$.

**[Partial Lean progress](partial_progress/README.md):** the complete $k=1$ case, finite Haar compression moments at every order up to the ambient dimension, and arbitrary-order inverse-Gram approximations are proved. These approximations give a vanishing-error finite formula for every fixed expected compression moment. For $k\ge2$ in the canonical floor-rank ensemble, the first and second compression moments converge almost surely; the second-moment proof derives a summable variance bound from exact fourth-order Haar integration. The limiting free-law identification, fluctuations at higher orders, and sharp spectral-outlier estimates remain unfinished. The random-channel conclusions depending on this input therefore remain conditional.


## Navigate the project

| Folder | Contents |
| --- | --- |
| [lean/](lean/) | Lean proofs grouped by mathematical topic |
| [results/](results/) | Numbered paper results, exact declarations, and complete source lists |
| [partial_progress/](partial_progress/) | Progress and remaining obligations for the unverified convergence theorem |
| [python/](python/) | Entropy cross-checks and the exact dimension-182 certificate |
| [verification/](verification/) | Current compiler logs, source hashes, axiom audit, and check outcomes |
| [scripts/](scripts/) | Rebuild, indexing, and verification commands |
| [archive/](archive/) | Earlier reports, supplied source versions, and historical logs |

The [verification guide](verification/README.md) explains how to inspect one
theorem and interpret the audit records. The [result index](results/RESULTS.json)
records conventions and corrections to the supplied draft.

## Citation

For this verification project, use:

```bibtex
@misc{wu_lean_2607_15210,
  author       = {Wu, Peixue},
  title        = {{Lean verification for counterexamples to additivity of minimum output p-Renyi entropy}},
  howpublished = {\href{https://github.com/pxwu24/superadditivity-of-classical-communication/tree/3b9d6132b9a14346ba716ba953d1e64151270eee/lean_arXiv_2607.15210}{Github Repository}}
}
```

Load `\usepackage{hyperref}` in your LaTeX preamble. The clickable bibliography
label is “Github Repository”. Verification records identify the checked source
files and dependency versions.
