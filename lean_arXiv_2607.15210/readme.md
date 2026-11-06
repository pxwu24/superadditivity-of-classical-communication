# Lean proofs and Python certificates

For [arXiv:2607.15210](https://arxiv.org/abs/2607.15210), *Counterexamples to
additivity of minimum output p-Rényi entropy of quantum channels for all p ≥ 0*.

**All 20 indexed mathematical results are verified in Lean**, including the
block-modified strong convergence theorem and its consequences for actual
finite-dimensional quantum channels. The convergence theorem is proved within
this project; the paper results require no external convergence assumption.

The complete audit covers **344 Lean modules and 4,378 declarations**, including
3,839 theorem declarations. All proofs use only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

| Folder | Contents |
| --- | --- |
| [lean/](lean/) | Formal proofs, build configuration, numbered result guides, and verification records |
| [python/](python/) | Numerical checks, exact arithmetic certificates, and their outputs |

## Results verified in Lean

Each link identifies the precise statement, its assumptions, and all related
Lean source files. The [result index](lean/results/RESULTS.json) also records
conventions and corrections to the supplied draft.

<!-- RESULT_TABLE_START -->
| Paper result | Verified statement |
| --- | --- |
| [Lemma II.2](lean/results/II_2.md) | Full local support of a Haar-random subspace |
| [Lemma II.3](lean/results/II_3.md) | Random compression formula |
| [Lemma A.1](lean/results/A_1.md) | Bernoulli free-convolution spectral edge |
| [Theorem III.1](lean/results/III_1.md) | Hausdorff limit of output state spaces |
| [Corollary III.2](lean/results/III_2.md) | One-copy entropy limit and asymptotics |
| [Lemma III.3](lean/results/III_3.md) | Support-function formula for trace-norm Hausdorff distance |
| [Lemma III.4](lean/results/III_4.md) | Channel support and generalized-eigenvalue threshold |
| [Theorem IV.1](lean/results/IV_1.md) | Limit of the Bell output |
| [Corollary IV.2](lean/results/IV_2.md) | Product-channel bound and Bell entropy expansion |
| [Lemma A.2](lean/results/A_2.md) | Second logarithmic variation |
| [Proposition A.3](lean/results/A_3.md) | Second moments after local normalization |
| [Proposition A.4](lean/results/A_4.md) | Asymptotic second Choi moment |
| [Theorem V.1](lean/results/V_1.md) | Single-output and Bell-output asymptotics after antisymmetric postprocessing |
| [Proposition V.2](lean/results/V_2.md) | Eigenvalue shuffling |
| [Proposition B.1](lean/results/B_1.md) | Entropy of the one-channel output body after antisymmetric postprocessing |
| [Proposition B.2](lean/results/B_2.md) | Entropy of the limiting Bell output after antisymmetric postprocessing |
| [Theorem I.1](lean/results/I_1.md) | Nonadditivity for every positive Renyi order |
| [Proposition VI.1](lean/results/VI_1.md) | Dimension-182 finite-channel consequence of the certified gap |
| [Lemma C.1](lean/results/C_1.md) | Reduction of the entropy minimum |
| [Lemma C.2](lean/results/C_2.md) | Scalar certificate for the largest eigenvalue |
<!-- RESULT_TABLE_END -->

<!-- CONDITIONAL_TABLE_START -->
<!-- CONDITIONAL_TABLE_END -->

The dimension-182 result gives finite-dimensional completely positive,
trace-preserving channel witnesses and the bound $k_{\mathrm{high}}(1)\le182$.

## Block-modified strong convergence

The completed theorem covers every positive output dimension, every limiting
rank density in $(0,1)$, and arbitrary integer rank sequences with that density
limit. It proves the Bernoulli free-sum limiting law, almost-sure affine
operator-norm convergence, and weak spectral convergence for signed real
coefficients and fixed output rotations. Only the Haar marginal laws are
required; the projection sequence need not be independent.

This is the affine-norm and weak-spectral statement used by the paper.
The [full theorem and proof guide](lean/CONVERGENCE.md) give its precise scope,
main declarations, and proof dependencies.

## Reproduce the verification

Install Git, Bash, Python 3.11 or newer with `venv`, and Lean's toolchain manager
[elan](https://github.com/leanprover/elan#installation). On Windows, use WSL.

```sh
git clone https://github.com/pxwu24/superadditivity-of-classical-communication.git
cd superadditivity-of-classical-communication
bash lean_arXiv_2607.15210/lean/verify-all.sh
```

The project pins Lean **4.19.0** and its Mathlib dependency. To recheck an
existing installation with four compilation jobs:

```sh
bash lean_arXiv_2607.15210/lean/verify-all.sh --no-setup --require-unconditional --jobs 4
```

The verifier rebuilds all maintained Lean sources, audits every declaration's
transitive axioms, checks preservation of the 54 original public entropy
statements, and runs the eight Python checks. The coverage check requires the
convergence proofs in the current audit and matching source hashes.

See the [verification records](lean/verification/README.md) for compiler logs,
source hashes, and instructions for inspecting an individual theorem.
Python certificates provide separate computational checks; the mathematical
results above have Lean proofs.

## Citation

```bibtex
@misc{wu_lean_2607_15210,
  author       = {Wu, Peixue},
  title        = {{Lean proofs and Python certificates for counterexamples to additivity of minimum output p-Renyi entropy}},
  howpublished = {\href{https://github.com/pxwu24/superadditivity-of-classical-communication/tree/main/lean_arXiv_2607.15210}{Github Repository}}
}
```

Load `\usepackage{hyperref}` in your LaTeX preamble. The bibliography displays
“Github Repository” as a clickable link.
