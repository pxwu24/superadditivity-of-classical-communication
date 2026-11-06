> Historical checkpoint. The full theorem is now proved; see the [completed proof guide](README.md).

# Blueprint formalization progress — November 5, 2026

**The full block-modified strong-convergence theorem is still unproved.**
All ten paper results remain conditional on block-modified strong convergence;
the concrete channel-existence development still assumes
`ProjectionChannels.Canonical.CanonicalStrongInput`. The definitions of that proposition,
`FullBlockModifiedStrongInput`, and `IsBernoulliFreeSumLaw` are unchanged.

The supplied archive contained a mathematical blueprint and finite Python
checks, but no new Lean proofs. The eleven modules below implement parts of
that blueprint as universal Lean theorems. They use no new axioms, `sorry`,
`admit`, or `native_decide`.

## Implemented components

| Blueprint component | Checked content | Sources |
| --- | --- | --- |
| A1 | Fixed-space interpretation of cycle count; permutation-length triangle inequality; absolute order; sign and genus parity | [Length](../lean/StrongConvergence/StrongConvergenceGenusLength.lean), [parity](../lean/StrongConvergence/StrongConvergenceGenusParity.lean) |
| A2 | Polynomial-matrix coefficient positivity, degree and parity filtration, stabilization of finite Neumann coefficients; specialization to the actual Haar Gram matrix | [Polynomial matrices](../lean/StrongConvergence/StrongConvergenceGenusNeumann.lean), [permutation specialization](../lean/StrongConvergence/StrongConvergencePermutationNeumann.lean) |
| A3; scalar parts of A6 | Quadratic radius, uniform row-error bounds, actual inverse-Gram remainder estimate, nonnegative polynomial tails, arbitrary-order scalar constants | [Radius and tails](../lean/StrongConvergence/StrongConvergenceGenusRadius.lean) |
| B6 deterministic step | Positivity eliminates the linear density term; quadratic bounds for convergent polynomial series; smooth edge detector | [Positive quadratic bounds](../lean/StrongConvergence/StrongConvergencePositiveQuadratic.lean) |
| D3 probability reduction | Vanishing upper-tail probabilities and summable centered deviations imply almost-sure upper bounds | [Probability upgrade](../lean/StrongConvergence/StrongConvergenceEdgeBootstrap.lean) |
| D3 deterministic assembly | Compact-support endpoint formula and affine norm convergence from two spectral-edge bounds and a lower bound | [Norm sandwich](../lean/StrongConvergence/StrongConvergenceEdgeSandwich.lean) |
| D4 | Output rotations preserve the actual canonical Haar sample measure; unrotated compression limits imply the precise rotated interface | [Output rotations](../lean/StrongConvergence/StrongConvergenceRotationTransfer.lean) |
| E5 and part of E6 | Bernoulli cumulant recurrence, formal quadratic and moment–cumulant identities, uniqueness, absolute convergence, evaluated quadratic, square-root branch identification | [Formal cumulants](../lean/StrongConvergence/StrongConvergenceFreeCumulant.lean), [analytic evaluation](../lean/StrongConvergence/StrongConvergenceFreeCumulantAnalytic.lean) |

A concrete new inverse-Gram estimate, for ambient dimension `N` and moment
order `m`, is

```math
\sum_\tau |\mathrm{Rem}_q(\sigma,\tau)|
\le 2\left(\frac{2m^2}{3N}\right)^q,
\qquad m\ge1,\quad N\ge2m^2.
```

Here `Rem` is the existing `inverseGramNeumannRemainder`, not a surrogate
random-matrix quantity. The declaration is
`TensorHaar.scaled_inverse_permutationGram_neumann_row_bound_quadratic`.
The scalar estimate used in A6(ii) is also proved for arbitrary positive `q`
under `1 ≤ m ≤ q` and `N ≥ 8q⁴`, replacing the blueprint's numerical checks
through `q = 60`.

For Bernoulli cumulants, the proof gives
`|κ_(n+1)(t)| ≤ 8^n` for `0 ≤ t ≤ 1`, absolute convergence for `|z| < 1/8`,
and identification with the existing `bernoulliDual t z` for `|z| ≤ 1/16`.
It uses Mathlib's multivariate-power-series substitution API specialized to
one variable. This avoids rebuilding formal substitution from scratch.

## What is still required

1. Complete the exact finite moment expansion and its degree-truncation error
   estimate, connecting the polynomial coefficients to normalized Haar moments.
   Scalar tail estimates alone do not establish this connection.
2. Prove the polynomial master inequality and smooth-test approximation with
   degree-uniform constants, then derive the vanishing outlier probabilities
   for the actual Haar ensemble.
3. Establish Gaussian concentration, the conditioning/whitening estimates,
   and their transfer to Haar compressions. The probability upgrade theorem
   requires summable concentration tails; it does not supply them.
4. Prove the permutation peel/moment recursion identifying the leading Haar
   moments with the free-sum cumulants. Construct the candidate compact law
   and establish its Cauchy-transform inverse germs on both sides.
5. Assemble `CanonicalStrongInput`, add unconditional downstream corollaries,
   and pass the unconditional coverage gate before changing completion claims.

The blueprint targets the canonical floor-rank sequence. Its density-error
argument uses `|d/N - t| < 1/N`; extending the conclusion to every rank sequence
with only `d/N → t` requires a separate argument. The canonical theorem would
suffice for the current paper's channel-existence conclusions.

## Verification

Run the repository's ordinary checks:

```sh
bash lean_arXiv_2607.15210/verify-all.sh --no-setup
```

The compiler and aggregate axiom audit include every maintained Lean module.
Allowed transitive axioms remain exactly `propext`, `Classical.choice`, and
`Quot.sound`. The machine-readable records are in
[verification](../verification/README.md).

The stricter command

```sh
python3 lean_arXiv_2607.15210/scripts/check_coverage.py --require-unconditional
```

must still fail: the requested strong-convergence theorem has not been
proved. Passing the ordinary build is not a substitute for this gate.
