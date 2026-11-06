#!/usr/bin/env python3
"""Exact finite Haar projection compression moments (standard library only).

Implements the formula proved in StrongConvergenceTensorCompressionCycles.lean.
All arithmetic is rational. This is a finite calculation, not a certificate of
the asymptotic spectral edge or the general strong-convergence theorem.

Example:
    normalized_moment(n=2, k=2, rank=2, a=[1, -1], order=3)

The permutation Gram matrix has size order!, so use small orders.
"""

from fractions import Fraction as Q
from itertools import permutations
from math import prod
import argparse
import json
from pathlib import Path


def cycles(p):
    unseen = set(range(len(p)))
    result = []
    while unseen:
        start = min(unseen)
        cycle, i = [], start
        while i in unseen:
            unseen.remove(i)
            cycle.append(i)
            i = p[i]
        result.append(tuple(cycle))
    return result


def compose(p, q):
    """p after q, matching Lean's multiplication of equivalences."""
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)


def solve(matrix, rhs):
    """Solve an invertible rational linear system by exact elimination."""
    size = len(rhs)
    aug = [[Q(x) for x in row] + [Q(b)] for row, b in zip(matrix, rhs)]
    for j in range(size):
        pivot = next((i for i in range(j, size) if aug[i][j]), None)
        if pivot is None:
            raise ValueError("Singular permutation Gram matrix")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        scale = aug[j][j]
        aug[j] = [x / scale for x in aug[j]]
        for i in range(size):
            if i != j and aug[i][j]:
                scale = aug[i][j]
                aug[i] = [x - scale * y for x, y in zip(aug[i], aug[j])]
    return [row[-1] for row in aug]


def gram_matrix(ambient_dimension, order):
    if not 0 <= order <= ambient_dimension:
        raise ValueError("The stable range requires 0 <= order <= n*k")
    perms = list(permutations(range(order)))
    gram = [[ambient_dimension ** len(cycles(compose(tau, inverse(sigma))))
             for tau in perms] for sigma in perms]
    return perms, gram


def normalized_moment(n, k, rank, a, order):
    """E[Tr((sum_i a_i P_ii)^order)] / n for a rank-rank Haar projection."""
    if n < 1 or k < 1 or len(a) != k or not 0 <= rank <= n * k:
        raise ValueError("Require n,k >= 1, len(a)=k and 0 <= rank <= n*k")
    if order == 0:
        return Q(1)
    a = tuple(Q(x) for x in a)
    perms, gram = gram_matrix(n * k, order)
    coefficients = solve(gram, [rank ** len(cycles(inverse(tau))) for tau in perms])
    gamma = tuple((j + 1) % order for j in range(order))
    answer = Q(0)
    for sigma, coefficient in zip(perms, coefficients):
        weight = prod(sum(x ** len(cycle) for x in a) for cycle in cycles(sigma))
        answer += coefficient * n ** len(cycles(compose(gamma, sigma))) * weight
    return answer / n


def require_equal(actual, expected, label):
    if actual != expected:
        raise ArithmeticError(f"{label}: {actual} != {expected}")


def run_checks():
    checked = []
    for n, k, rank, a in [(2, 2, 2, [1, -1]), (2, 3, 3, [Q(1, 2), -2, 3]),
                           (3, 2, 4, [-1, 2]), (1, 3, 2, [2, -1, Q(3, 2)])]:
        N = n * k
        first = Q(rank, N) * sum(a)
        aa = Q(rank * (N * rank - 1), N * (N * N - 1))
        bb = Q(rank * (N - rank), N * (N * N - 1))
        second = aa * sum(a) ** 2 + n * bb * sum(x * x for x in a)
        require_equal(normalized_moment(n, k, rank, a, 1), first, "first moment")
        require_equal(normalized_moment(n, k, rank, a, 2), second, "second moment")
        checked.append({"n": n, "k": k, "rank": rank,
                        "first": str(first), "second": str(second)})

    # Endpoint projections and the separate rank-one (unit-vector) formula.
    n, k, a = 2, 2, [Q(2), Q(-1, 3)]
    for order in range(1, 5):
        require_equal(normalized_moment(n, k, 0, a, order), 0, "zero projection")
        require_equal(normalized_moment(n, k, n * k, a, order),
                      sum(a) ** order, "identity projection")
        gamma = tuple((j + 1) % order for j in range(order))
        numerator = sum(n ** len(cycles(compose(gamma, sigma))) *
                        prod(sum(x ** len(c) for x in a) for c in cycles(sigma))
                        for sigma in permutations(range(order)))
        rank_one = Q(numerator, n * prod(n * k + j for j in range(order)))
        require_equal(normalized_moment(n, k, 1, a, order), rank_one, "rank one")

    # Independently enumerate the Gram row and its inverse for the proved bound.
    N, order = 17, 3
    perms, gram = gram_matrix(N, order)
    epsilon = prod(Q(N + j, N) for j in range(order)) - 1
    normalized_rows = [sum(abs(Q(g, N ** order) - (i == j))
                           for j, g in enumerate(row)) for i, row in enumerate(gram)]
    for row in normalized_rows:
        require_equal(row, epsilon, "exact normalized Gram row")
    columns = [solve(gram, [int(i == j) for i in range(len(perms))])
               for j in range(len(perms))]
    inverse_errors = [sum(abs(N ** order * columns[j][i] - (i == j))
                          for j in range(len(perms))) for i in range(len(perms))]
    if not 0 <= epsilon < 1 or max(inverse_errors) > epsilon / (1 - epsilon):
        raise ArithmeticError("The inverse Gram row bound failed")
    return {"status": "pass", "arithmetic": "exact rational",
            "scope": "Finite Haar moment formula checks, not asymptotic convergence",
            "low_moments": checked, "endpoint_and_rank_one_orders": [1, 2, 3, 4],
            "gram_bound": {"dimension": N, "order": order,
                           "epsilon": str(epsilon),
                           "inverse_error": str(max(inverse_errors)),
                           "bound": str(epsilon / (1 - epsilon))}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(run_checks(), indent=2) + "\n"
    if args.output:
        args.output.write_text(report)
    print(report, end="")
