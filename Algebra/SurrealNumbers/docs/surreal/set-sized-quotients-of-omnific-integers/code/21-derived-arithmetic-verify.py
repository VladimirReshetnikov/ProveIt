#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex (Python 3.9+, standard library).

These checks do NOT prove infinite-support assertions, nonzero Ext classes, or
projective dimensions. They check signs, finite telescope identities, integer
multiplication kernels, and the explicit arithmetic examples used in the proofs.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import argparse


def add_term(out, key, value):
    out[key] = out.get(key, 0) + value
    if out[key] == 0:
        del out[key]


def add_exp(a, b):
    return tuple(x + y for x, y in zip(a, b))


def koszul_boundary(terms, dimension, q):
    out = {}
    for (subset, exponent), coefficient in terms.items():
        for j, i in enumerate(subset):
            e = tuple(q if a == i else F(0) for a in range(dimension))
            target = (subset[:j] + subset[j + 1:], add_exp(exponent, e))
            add_term(out, target, (-1) ** j * coefficient)
    return out


def transition(terms, dimension, delta):
    out = {}
    for (subset, exponent), coefficient in terms.items():
        e = tuple(delta if a in subset else F(0) for a in range(dimension))
        add_term(out, (subset, add_exp(exponent, e)), coefficient)
    return out


def rank(matrix):
    if not matrix:
        return 0
    a = [[F(x) for x in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    r = 0
    for col in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        v = a[r][col]
        a[r] = [x / v for x in a[r]]
        for i in range(rows):
            if i != r and a[i][col]:
                v = a[i][col]
                a[i] = [x - v * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == rows:
            break
    return r


def determinant(matrix):
    a = [[F(x) for x in row] for row in matrix]
    n = len(a)
    result = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        v = a[j][j]
        result *= v
        for i in range(j + 1, n):
            ratio = a[i][j] / v
            for k in range(j + 1, n):
                a[i][k] -= ratio * a[j][k]
    return result


def matvec(matrix, vector):
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def transpose(columns):
    return list(map(list, zip(*columns)))


def monogenic_order(lower_coefficients):
    """Return multiplication for Z[x]/(x^r + sum c_j*x^j)."""
    r = len(lower_coefficients)

    def power(n):
        terms = [0] * max(r, n + 1)
        terms[n] = 1
        for d in range(len(terms) - 1, r - 1, -1):
            c = terms[d]
            if c:
                terms[d] = 0
                for j, b in enumerate(lower_coefficients):
                    terms[d - r + j] -= c * b
        return terms[:r]

    products = [power(i + j) for i in range(r) for j in range(r)]
    mu = transpose(products)
    kernel_basis = []
    # Every nonzero first-index coordinate is a pivot. Thus this is an
    # integral basis, not merely a rationally independent list of relations.
    for i in range(1, r):
        for j in range(r):
            v = [0] * (r * r)
            v[i * r + j] = 1
            for h, c in enumerate(products[i * r + j]):
                v[h] -= c
            assert not any(matvec(mu, v))
            kernel_basis.append(v)
    assert rank(transpose(kernel_basis)) == r * (r - 1) if kernel_basis else True
    assert rank(mu) == r
    # Trace of multiplication by each power-basis vector.
    traces = [sum(products[i * r + j][j] for j in range(r)) for i in range(r)]
    gram = [[sum(c * t for c, t in zip(products[i * r + j], traces))
             for j in range(r)] for i in range(r)]
    skew = []
    for i, j in combinations(range(r), 2):
        v = [0] * (r * r)
        v[i * r + j], v[j * r + i] = 1, -1
        assert not any(matvec(mu, v))
        skew.append(v)
    sym_relations = []
    for i in range(1, r):
        for j in range(i, r):
            v = [0] * (r * r)
            v[i * r + j] = 1
            for h, c in enumerate(products[i * r + j]):
                v[h] -= c
            assert not any(matvec(mu, v))
            sym_relations.append(v)
    combined = skew + sym_relations
    assert rank(transpose(combined)) == r * (r - 1) if combined else True
    return {
        "polynomial_lower_coefficients": lower_coefficients,
        "rank": r,
        "multiplication_matrix": mu,
        "integral_kernel_basis": kernel_basis,
        "tor2_rank": r * r - rank(mu),
        "product_submodule_rank": len(skew),
        "degree2_indecomposable_rank": len(sym_relations),
        "trace_gram_matrix": gram,
        "discriminant": int(determinant(gram)),
    }


def run():
    chain_checks = 0
    for d in range(1, 7):
        zero = (F(0),) * d
        for n in range(4):
            q, qnext = F(1, 2 ** n), F(1, 2 ** (n + 1))
            for p in range(d + 1):
                for subset in combinations(range(d), p):
                    e = {(subset, zero): 1}
                    assert not koszul_boundary(koszul_boundary(e, d, q), d, q)
                    lhs = koszul_boundary(transition(e, d, q - qnext), d, qnext)
                    rhs = transition(koszul_boundary(e, d, q), d, q - qnext)
                    assert lhs == rhs
                    chain_checks += 2
    # Finite versions of y_n - u_n*y_{n+1} = c_n and the support barrier.
    telescope_checks = 0
    for length in range(1, 25):
        constants = [(-1) ** n * (n + 1) for n in range(length)]
        y = []
        for n in range(length + 1):
            yn = {}
            for j in range(n, length):
                add_term(yn, F(1, 2 ** n) - F(1, 2 ** j), constants[j])
            y.append(yn)
        for n in range(length):
            delta = F(1, 2 ** n) - F(1, 2 ** (n + 1))
            diff = dict(y[n])
            for exponent, coefficient in y[n + 1].items():
                add_term(diff, exponent + delta, -coefficient)
            assert diff == {F(0): constants[n]}
            barrier = F(1) - F(1, 2 ** (n + 1))
            assert all(F(1) - F(1, 2 ** j) < barrier for j in range(n + 1))
            telescope_checks += 2
    orders = {
        "Z[sqrt(2)]": monogenic_order([-2, 0]),
        "Z[sqrt(3)]": monogenic_order([-3, 0]),
        "Z[cuberoot(2)]": monogenic_order([-2, 0, 0]),
        "Z[golden_ratio]": monogenic_order([-1, -1]),
    }
    assert orders["Z[sqrt(2)]"]["discriminant"] == 8
    assert orders["Z[sqrt(3)]"]["discriminant"] == 12
    assert orders["Z[cuberoot(2)]"]["discriminant"] == -108
    assert orders["Z[golden_ratio]"]["discriminant"] == 5
    # In the basis 1,sqrt(2),sqrt(3),sqrt(6), the pair product has rank four.
    distinct_quadratics_mu = [[1, 0, 0, 0], [0, 0, 1, 0],
                              [0, 1, 0, 0], [0, 0, 0, 1]]
    assert rank(distinct_quadratics_mu) == 4
    return {
        "status": "All exact finite checks passed",
        "scope_warning": "Not a proof assistant verification and not a proof of infinite Ext nonvanishing.",
        "koszul_and_transition_identities_checked": chain_checks,
        "finite_telescope_and_support_checks": telescope_checks,
        "orders": orders,
        "quadratic_pair": {"fields": ["Q(sqrt(2))", "Q(sqrt(3))"],
                           "product_rank": 4, "tor2_rank": 0},
        "self_quadratic_pair": {"field": "Q(sqrt(2))", "product_rank": 2,
                                "tor2_rank": 2},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    print("Koszul/transition checks:", result["koszul_and_transition_identities_checked"])
    print("Telescope/support checks:", result["finite_telescope_and_support_checks"])
    print("Wrote", args.output)


if __name__ == "__main__":
    main()
