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

For arXiv:2607.15210, the block-modified strong-convergence statement is now
proved, including the limiting law, affine operator-norm convergence, and weak
spectral convergence for arbitrary admissible rank sequences. The paper's
random-channel limits and finite-channel existence results no longer assume
this theorem. See the [proof guide](lean_arXiv_2607.15210/partial_progress/README.md)
and [verification records](lean_arXiv_2607.15210/verification/README.md).

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
