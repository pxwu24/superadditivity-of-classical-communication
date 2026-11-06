# Current verification records

| Record | Meaning |
| --- | --- |
| [verification_status.json](verification_status.json) | Compiler outcome, versions, hashes, and declaration counts |
| [source_manifest.json](source_manifest.json) | Every rebuilt Lean source and its imports |
| [axiom_audit.log](axiom_audit.log) | Transitive axiom audit of all maintained declarations |
| [result_sources.json](result_sources.json) | Numbered results and complete local source dependencies |
| [convergence_status.json](convergence_status.json) | Completed convergence theorem and final proof endpoints |
| [convergence_sources.json](convergence_sources.json) | Full import closures for the convergence proof |
| [paper_coverage.json](paper_coverage.json) | Unconditional coverage and audited convergence declarations |
| [python_verification.json](../../python/verification/python_verification.json) | Python check outcomes and source hashes |
| [entropy_statements.json](entropy_statements.json) | Comparison with the 54 original public entropy statements |
| [exit_code.txt](exit_code.txt) | Last full verifier exit code |

The convergence theorem and its paper corollaries are now included in the
kernel audit. The strict coverage check verifies the named input declarations
and that the audited source hashes match every maintained Lean file:

```sh
cd lean_arXiv_2607.15210/lean
python3 scripts/check_coverage.py --require-unconditional
```

The expected exit code is 0 after a successful complete rebuild.

## Inspect a theorem

After running the full verifier, enter `lean_arXiv_2607.15210/lean/` and run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs
#check HaarProjection.haar_projection_partialTrace_rank_fin
#print axioms HaarProjection.haar_projection_partialTrace_rank_fin
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The [numbered guides](../results/) provide the exact declaration names.
To rebuild an individual source, after its dependencies have been built:

```sh
lake env lean --root=src src/Dimension182/RevisionScalarCertificate.lean
```

[Back to the verification summary](../../readme.md)
