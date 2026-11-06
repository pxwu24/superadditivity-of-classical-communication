# Lean verification

This directory is the standalone Lean project for all 20 indexed results of
arXiv:2607.15210, including block-modified strong convergence and the resulting
finite-dimensional channel witnesses.

| Location | Contents |
| --- | --- |
| [src/](src/) | 344 proof and audit modules, grouped by topic |
| [CONVERGENCE.md](CONVERGENCE.md) | Full convergence statement and proof guide |
| [results/](results/) | Numbered results, declarations, and source dependencies |
| [verification/](verification/) | Compiler records, source hashes, and axiom audit |
| [scripts/](scripts/) | Rebuild, indexing, and coverage tools |

From this directory, run:

```sh
bash verify-all.sh
```

With dependencies already installed:

```sh
bash verify-all.sh --no-setup --jobs 4
```

The verifier checks every maintained source and declaration, all indexed paper
results, and the companion [Python certificates](../python/). Lean 4.19.0 and
Mathlib are pinned by the committed toolchain and manifest.

[Project summary](../readme.md)
