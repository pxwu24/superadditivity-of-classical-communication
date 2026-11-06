# Verification tools

Run `bash lean_arXiv_2607.15210/lean/verify-all.sh` from the repository root.
Use `--no-setup` to reuse installed dependencies and `--jobs 4` to run up to four
independent Lean compiler processes.

- `verify_lean.py`: rebuild every module in `../src/` and audit transitive axioms.
- `result_index.py`: regenerate numbered result guides and source dependencies.
- `verify_entropy_statements.py`: check preservation of all 54 original entropy theorem statements.
- `check_coverage.py`: require the convergence proof in the current audit and verify source hashes.

The combined verifier also runs [`python/verify.py`](../../python/verify.py),
which checks the numerical calculations and exact finite certificates.

These scripts support the [main verification guide](../../readme.md).
