# Exact finite Haar moments

[exact_haar_moments.py](exact_haar_moments.py) evaluates finite Haar projection
compression moments using rational arithmetic and the permutation Gram
matrix. It implements the formula proved in
[StrongConvergenceTensorCompressionCycles.lean](../../lean/src/StrongConvergence/StrongConvergenceTensorCompressionCycles.lean).

Run its self-checks from this directory:

```sh
python3 exact_haar_moments.py --output exact_haar_moments_results.json
```

The [Python verifier](../verify.py) includes these checks in the full run.
The [convergence proof guide](../../lean/CONVERGENCE.md) describes the Lean
proof of the asymptotic theorem.
