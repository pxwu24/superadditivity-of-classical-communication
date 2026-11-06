# Lemma II.2: Full local support of a Haar-random subspace

Complete.

Actual unitary Haar probability measure, projection conjugation, partial-trace rank min(n,k*d), and almost-sure positive-definiteness iff n<=k*d.

## Check this result

First run `bash lean_arXiv_2607.15210/lean/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/lean/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check HaarProjection.haar_projection_partialTrace_rank_fin
#print axioms HaarProjection.haar_projection_partialTrace_rank_fin
#check HaarProjection.haar_projection_full_local_support_iff_fin
#print axioms HaarProjection.haar_projection_full_local_support_iff_fin
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. The entry declarations include the completed paper endpoints.

## Entry files

- [HaarProjections.HaarFullLocalSupport](../src/HaarProjections/HaarFullLocalSupport.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [src/HaarProjections/GaussianMatrixLaw.lean](../src/HaarProjections/GaussianMatrixLaw.lean)
- [src/HaarProjections/GaussianRadial.lean](../src/HaarProjections/GaussianRadial.lean)
- [src/HaarProjections/GaussianRank.lean](../src/HaarProjections/GaussianRank.lean)
- [src/HaarProjections/GaussianUnitary.lean](../src/HaarProjections/GaussianUnitary.lean)
- [src/HaarProjections/GaussianWhitening.lean](../src/HaarProjections/GaussianWhitening.lean)
- [src/HaarProjections/HaarFullLocalSupport.lean](../src/HaarProjections/HaarFullLocalSupport.lean)
- [src/HaarProjections/HaarLocalSupport.lean](../src/HaarProjections/HaarLocalSupport.lean)
- [src/HaarProjections/HaarMeasure.lean](../src/HaarProjections/HaarMeasure.lean)
- [src/HaarProjections/HaarOrbitUnique.lean](../src/HaarProjections/HaarOrbitUnique.lean)
- [src/HaarProjections/HaarProjection.lean](../src/HaarProjections/HaarProjection.lean)
- [src/HaarProjections/MatrixRankMeasurable.lean](../src/HaarProjections/MatrixRankMeasurable.lean)
- [src/HaarProjections/ProjectionOrbit.lean](../src/HaarProjections/ProjectionOrbit.lean)
- [src/Preliminaries/PreliminariesMatrix.lean](../src/Preliminaries/PreliminariesMatrix.lean)

## Assumptions and dependencies

- n,k,d natural, 1<=d<=n*k; P0 Hermitian idempotent of rank d. No external Gaussian/Haar rank premise.
