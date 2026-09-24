#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These are finite algebra and indexing checks, not formal verification of the
infinite Hahn-support, cofinality, factorization, or non-Bézout theorems.
Python 3.10+; standard library only. The output path is explicit to avoid
unintentionally overwriting a delivered verification record.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import sys
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from typing import Iterable

Vec = tuple[Q, ...]
Poly = tuple[Q, ...]  # low degree first; zero is ()


def vadd(a: Vec, b: Vec) -> Vec:
    if len(a) != len(b):
        raise ValueError("Coordinate dimensions differ")
    return tuple(x + y for x, y in zip(a, b))


def vscale(a: Vec, c: int | Q) -> Vec:
    return tuple(Q(c) * x for x in a)


def vkey(a: Vec) -> tuple[Q, ...]:
    """Reverse lexicographic ordering: largest index is dominant."""
    return tuple(reversed(a))


def finite_hahn_valuation(terms: Iterable[tuple[Vec, Q]]) -> Vec:
    coefficients: dict[Vec, Q] = {}
    for exponent, coefficient in terms:
        coefficients[exponent] = coefficients.get(exponent, Q(0)) + coefficient
    support = [e for e, c in coefficients.items() if c]
    if not support:
        raise ValueError("Valuation of zero was requested without an infinity type")
    return min(support, key=vkey)


def poly(values: Iterable[int | Q]) -> Poly:
    result = [Q(v) for v in values]
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def padd(a: Poly, b: Poly) -> Poly:
    return poly((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def pscale(a: Poly, c: int | Q) -> Poly:
    return poly(Q(c) * x for x in a)


def pmul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return ()
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return poly(out)


def ptrunc(a: Poly, order: int) -> Poly:
    return poly(a[:order])


def ppow(a: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("Polynomial exponent must be nonnegative")
    result = poly([1])
    while n:
        if n & 1:
            result = pmul(result, a)
        a = pmul(a, a)
        n //= 2
    return result


def pshift(a: Poly, x: Q) -> Poly:
    """Return a(X+x), exactly."""
    result: Poly = ()
    for coefficient in reversed(a):
        result = padd(pmul(result, poly([x, 1])), poly([coefficient]))
    return result


def pdivmod(a: Poly, p: Poly) -> tuple[Poly, Poly]:
    if not p:
        raise ZeroDivisionError("Polynomial divisor is zero")
    r = list(a)
    q = [Q(0)] * max(0, len(a) - len(p) + 1)
    while r and len(r) >= len(p):
        k = len(r) - len(p)
        c = r[-1] / p[-1]
        q[k] += c
        for j, pj in enumerate(p):
            r[k + j] -= c * pj
        while r and r[-1] == 0:
            r.pop()
    return poly(q), poly(r)


def t_product(a: list[Poly], b: list[Poly], order: int) -> list[Poly]:
    """Multiply modulo t**order; coefficients are polynomials in X."""
    out: list[Poly] = [()] * order
    for i, ai in enumerate(a[:order]):
        for j, bj in enumerate(b[:order - i]):
            out[i + j] = padd(out[i + j], pmul(ai, bj))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checks: list[dict[str, object]] = []
    examples: dict[str, object] = {}

    def check(category: str, name: str, condition: bool) -> None:
        checks.append({"category": category, "name": name, "passed": bool(condition)})
        if not condition:
            raise AssertionError(f"{category}: {name}")

    # Exact exponent arithmetic for the explicit rank-infinite example,
    # restricted to the first nine coordinates for finite checks.
    dim = 9
    zero = (Q(0),) * dim
    basis = [tuple(Q(int(i == j)) for i in range(dim)) for j in range(dim)]
    N = 8
    lambda_rows = []
    for n in range(1, N + 1):
        en, enext = basis[n - 1], basis[n]
        total = zero
        for j in range(1, N + 1):
            ej, ejnext = basis[j - 1], basis[j]
            # 1 - rho_n/sigma_j = (sigma_j-rho_n)/sigma_j.
            numerator_v = finite_hahn_valuation([
                (vscale(ej, -1), Q(1)), (ejnext, Q(1)),
                (vscale(en, -1), Q(-1)),
            ])
            actual = vadd(numerator_v, ej)
            expected = (vadd(ej, vscale(en, -1)) if j < n else
                        vadd(enext, en) if j == n else zero)
            check("paired roots", f"factor valuation n={n}, j={j}", actual == expected)
            total = vadd(total, actual)
        formula = vadd(enext, vscale(en, 2 - n))
        for j in range(n - 1):
            formula = vadd(formula, basis[j])
        check("paired roots", f"lambda formula n={n}", total == formula)
        for k in [1, 2, 10, 100, 10000]:
            check("finite dominance samples", f"lambda_{n}>{k}*e_{n}",
                  vkey(total) > vkey(vscale(en, k)))
        lambda_rows.append({"n": n, "coordinates_low_first": [str(x) for x in total]})
    examples["lambda_values"] = lambda_rows

    # Coefficients of the first N factors of f, computed from actual subsets.
    for length in range(1, N + 1):
        for k in range(length + 1):
            exponents = []
            for indices in itertools.combinations(range(length), k):
                exponent = zero
                for j in indices:
                    exponent = vadd(exponent, basis[j])
                exponents.append(exponent)
            smallest = min(exponents, key=vkey)
            expected = zero
            for j in range(k):
                expected = vadd(expected, basis[j])
            check("product coefficients", f"leading exponent length={length}, degree={k}",
                  smallest == expected)
            check("product coefficients", f"unique leading subset length={length}, degree={k}",
                  exponents.count(smallest) == 1)

    # Finite Hahn preparation in the special exponent group Z, modulo t^order.
    # Ordinary t-adic truncation is NOT claimed to represent arbitrary ranks.
    rng = random.Random(20260921)
    order = 9
    prep_examples = []
    for trial in range(24):
        d = trial % 5
        P = poly([rng.randint(-3, 3) for _ in range(d)] + [1])
        A = [P] + [poly(rng.randint(-3, 3) for _ in range(rng.randint(1, 7)))
                   for _ in range(1, order)]
        W: list[Poly] = [P] + [()] * (order - 1)
        U: list[Poly] = [poly([1])] + [()] * (order - 1)
        for eta in range(1, order):
            cross: Poly = ()
            for alpha in range(1, eta):
                cross = padd(cross, pmul(W[alpha], U[eta - alpha]))
            H = padd(A[eta], pscale(cross, -1))
            U[eta], W[eta] = pdivmod(H, P)
            check("preparation", f"degree bound trial={trial}, exponent={eta}",
                  len(W[eta]) <= d)
            check("preparation", f"division identity trial={trial}, exponent={eta}",
                  padd(pmul(P, U[eta]), W[eta]) == H)
        check("preparation", f"product modulo t^{order}, trial={trial}",
              t_product(W, U, order) == A)
        # Independently reconstruct the unit inverse through the coefficient recurrence.
        V: list[Poly] = [poly([1])] + [()] * (order - 1)
        for eta in range(1, order):
            total_p: Poly = ()
            for alpha in range(1, eta + 1):
                total_p = padd(total_p, pmul(U[alpha], V[eta - alpha]))
            V[eta] = pscale(total_p, -1)
        check("preparation", f"unit inverse modulo t^{order}, trial={trial}",
              t_product(U, V, order) == [poly([1])] + [()] * (order - 1))
        check("preparation", f"recover W from A and inverse, trial={trial}",
              t_product(A, V, order) == W)
        if trial < 2:
            prep_examples.append({"trial": trial, "P": [str(q) for q in P],
                                  "W_mod_t3": [[str(q) for q in p] for p in W[:3]],
                                  "U_mod_t3": [[str(q) for q in p] for p in U[:3]]})
    examples["preparation_samples"] = prep_examples

    # Local inverse jets in the Hermite damping construction.
    for m in range(1, 8):
        for Npower in [0, 1, 2, 5, 13]:
            x = Q(m + 2)
            B = poly(Q((j + 1) * (-1)**j, j + 2) for j in range(m))
            negative = poly((Q(1) if k == 0 else Q((-1)**k * math.comb(Npower + k - 1, k)))
                            / x**k if Npower else Q(int(k == 0))
                            for k in range(m))
            r = ptrunc(pmul(B, negative), m)
            positive = ptrunc(ppow(poly([1, 1 / x]), Npower), m)
            check("inverse jets", f"inverse identity m={m}, N={Npower}",
                  ptrunc(pmul(r, positive), m) == B)
            previous_nodes = [Q(-2), Q(-1), Q(1)]
            Qprev = poly([1])
            for node in previous_nodes:
                Qprev = pmul(Qprev, ppow(poly([-node, 1]), 2))
            correction = pmul(pmul(Qprev, ppow(poly([0, 1 / x]), Npower)), pshift(r, -x))
            for node in previous_nodes:
                check("inverse jets", f"previous double zero m={m}, N={Npower}, node={node}",
                      not ptrunc(pshift(correction, node), 2))
            actual_jet = ptrunc(pshift(correction, x), m)
            expected_jet = ptrunc(pmul(pshift(Qprev, x), B), m)
            check("inverse jets", f"new residual jet m={m}, N={Npower}", actual_jet == expected_jet)

    counts = dict(Counter(str(c["category"]) for c in checks))
    report = {
        "description": "Exact finite checks; not a verification of the infinite theorems",
        "python_version": sys.version.split()[0],
        "seed": 20260921,
        "arithmetic": "fractions.Fraction; no floating point",
        "checks_total": len(checks),
        "checks_passed": sum(bool(c["passed"]) for c in checks),
        "categories": counts,
        "examples": examples,
        "checks": checks,
        "limitations": [
            "Finite dominance samples do not prove domination of every integer multiple.",
            "Finite products cannot witness the global non-Bezout theorem.",
            "Preparation checks are modulo t^9 in an integer exponent subgroup.",
            "No proof assistant, novelty verifier, or infinite-support decision procedure is used.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{report['checks_passed']}/{report['checks_total']} finite checks passed")
    print(json.dumps(counts, indent=2))
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
