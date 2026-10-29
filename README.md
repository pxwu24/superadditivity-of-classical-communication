# Superadditivity of classical communication
This repository provides Lean verification of the following arXiv papers, alongside Python codes for numerical calculations if needed.

| Paper | Available files |
| --- | --- |
| arXiv:2607.15210 | [Lean proofs and Python certificates](./lean_arXiv_2607.15210/README.md) |
| arXiv:2608.25961 | [Lean proofs and Python certificates](reproduce_numerics.py) |
| arXiv:2609.26743 | [Lean proofs and Python certificates](./lean_arXiv:2609.26743/README.md) |

For arXiv:2609.26743, the Lean project formalizes all the results, including the Supplement and the main
theorem of *Explicit channels with unbounded gains in classical communication
using entangled inputs*.

For arXiv:2608.25961, the linked file currently provides a Python numerical reproducibility code.

For arXiv:2607.15210, the finite-dimensional results are verified in Lean;
the random-channel conclusions retain the block-modified strong-convergence
hypothesis from [Nechita, Theorem 5.2](https://arxiv.org/pdf/1802.00067).
[Verified progress](lean_arXiv_2607.15210/partial_progress/README.md) includes
almost-sure first and second compression moments for the canonical ensemble,
exact finite Haar moments at every order, and arbitrary-order inverse-Gram
approximations. The general limiting-law identification and sharp
spectral-outlier estimates remain unproved in Lean.

## Citation

For the Lean verification of arXiv:2609.26743, use:

```bibtex
@misc{wu_lean_2609_26743,
  author       = {Wu, Peixue},
  title        = {{Lean verification for explicit channels with unbounded gains in classical communication using entangled inputs}},
  howpublished = {\href{https://github.com/pxwu24/superadditivity-of-classical-communication/tree/5f4ddefcb814141acdf2a8957beb4f7c7382e86d/lean_arXiv:2609.26743}{Github Repository}}
}
```

Load `\usepackage{hyperref}` in your LaTeX preamble. The bibliography displays
only the clickable label “Github Repository”; the link identifies a fixed
code snapshot without printing its URL or commit hash.
