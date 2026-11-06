# Python checks and certificates

These numerical checks and exact arithmetic certificates complement the
[Lean proofs](../lean/). The paper results, including block-modified strong
convergence, are verified in Lean; numerical checks provide reproducible
finite-dimensional comparisons.

| Folder | Contents |
| --- | --- |
| [random_compression/](random_compression/) | Compression spectral-edge comparisons |
| [entropy/](entropy/) | Entropy asymptotics and antisymmetric output spectra |
| [bell_output/](bell_output/) | Bell-output identities and finite-dimensional checks |
| [nonadditivity/](nonadditivity/) | Main nonadditivity coefficient inequalities |
| [dimension_182/](dimension_182/) | Exact rational certificate and exploratory calculations |
| [haar_moments/](haar_moments/) | Exact finite Haar projection moments |
| [verification/](verification/) | Results, source hashes, and logs for all eight checks |

From this directory, install the pinned dependencies and run all checks:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python verify.py
```

To run the combined Lean and Python verification from the repository root:

```sh
bash lean_arXiv_2607.15210/lean/verify-all.sh
```

The exact dimension-182 certificate uses only Python's standard library:

```sh
python3 dimension_182/certify_k182_exact.py
```

It certifies a scalar gap greater than 477/1000000 nats at
$t=27/100000$. The finite Haar-moment checker also uses exact rational
arithmetic. The remaining checks use numerical calculations.

[Back to the project](../readme.md)
