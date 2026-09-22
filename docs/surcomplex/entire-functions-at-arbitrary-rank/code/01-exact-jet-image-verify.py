#!/usr/bin/env python3
"""Finite exact checks accompanying the infinite jet-image manuscript.

Python 3.10+; standard library only. These tests verify finite algebra and
finite ordered-group calculations, NOT any infinite existence/nonexistence
claim or the correctness of the full mathematical proofs.

Run: python3 verify.py --output checks-rerun.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import json
import random

Poly = tuple[F, ...]       # Increasing powers; zero is ().
Vector = tuple[F, ...]     # Largest nonzero coordinate is most significant.
ZERO: Poly = ()
ONE: Poly = (F(1),)
T: Poly = (F(0), F(1))


def poly(items) -> Poly:
    result = [F(x) for x in items]
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def add(a: Poly, b: Poly) -> Poly:
    return poly((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def scale(a: Poly, s: F) -> Poly:
    return poly(x * s for x in a)


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, scale(b, F(-1)))


def mul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return ZERO
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return poly(out)


def power(a: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("Polynomial exponent must be nonnegative")
    out = ONE
    while n:
        if n & 1:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def divrem(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    if not b:
        raise ZeroDivisionError("Zero polynomial divisor")
    r = list(a)
    q = [F(0)] * max(0, len(a) - len(b) + 1)
    while r and len(r) >= len(b):
        shift = len(r) - len(b)
        factor = r[-1] / b[-1]
        q[shift] += factor
        for j, coeff in enumerate(b):
            r[j + shift] -= factor * coeff
        while r and r[-1] == 0:
            r.pop()
    return poly(q), poly(r)


def rem(a: Poly, b: Poly) -> Poly:
    return divrem(a, b)[1]


def invmod(a: Poly, modulus: Poly) -> Poly:
    if len(modulus) < 2:
        raise ValueError("Modulus must have positive degree")
    r0, r1 = modulus, rem(a, modulus)
    s0, s1 = ZERO, ONE
    while r1:
        q, r2 = divrem(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, sub(s0, mul(q, s1))
    if len(r0) != 1:
        raise ValueError("Class is not a unit modulo the polynomial")
    return rem(scale(s0, 1 / r0[0]), modulus)


def evaluate(a: Poly, x: F) -> F:
    out = F(0)
    for c in reversed(a):
        out = out * x + c
    return out


def hasse(a: Poly, x: F, order: int) -> F:
    if order < 0:
        raise ValueError("Jet order must be nonnegative")
    return sum((F(comb(k, order)) * a[k] * x ** (k - order)
                for k in range(order, len(a))), F(0))


def root_product(nodes: list[tuple[F, int]]) -> Poly:
    out = ONE
    for x, multiplicity in nodes:
        if multiplicity <= 0:
            raise ValueError("Root multiplicities must be positive")
        out = mul(out, power(poly([-x, 1]), multiplicity))
    return out


def solve(matrix: list[list[F]], rhs: list[F]) -> list[F]:
    n = len(matrix)
    if len(rhs) != n or any(len(row) != n for row in matrix):
        raise ValueError("Expected a square system")
    a = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            raise ValueError("Singular system")
        a[j], a[pivot] = a[pivot], a[j]
        p = a[j][j]
        a[j] = [x / p for x in a[j]]
        for i in range(n):
            if i != j and a[i][j]:
                factor = a[i][j]
                a[i] = [x - factor * y for x, y in zip(a[i], a[j])]
    return [a[i][-1] for i in range(n)]


def hermite(nodes: list[tuple[F, list[F]]]) -> Poly:
    if len({x for x, _ in nodes}) != len(nodes):
        raise ValueError("Hermite nodes must be distinct")
    degree_bound = sum(len(jets) for _, jets in nodes)
    matrix: list[list[F]] = []
    rhs: list[F] = []
    for x, jets in nodes:
        for order, value in enumerate(jets):
            matrix.append([F(comb(k, order)) * x ** (k - order)
                           if k >= order else F(0)
                           for k in range(degree_bound)])
            rhs.append(value)
    return poly(solve(matrix, rhs))


def determinant(matrix: list[list[F]]) -> F:
    a = [row[:] for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("Expected square matrix")
    value = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            value = -value
        p = a[j][j]
        value *= p
        for i in range(j + 1, n):
            factor = a[i][j] / p
            for k in range(j + 1, n):
                a[i][k] -= factor * a[j][k]
    return value


def multiplication_matrix(r: Poly, modulus: Poly) -> list[list[F]]:
    n = len(modulus) - 1
    columns = [rem(mul(r, power(T, j)), modulus) for j in range(n)]
    return [[columns[j][i] if i < len(columns[j]) else F(0)
             for j in range(n)] for i in range(n)]


def vadd(a: Vector, b: Vector) -> Vector:
    return tuple(x + y for x, y in zip(a, b))


def vscale(a: Vector, s: F) -> Vector:
    return tuple(x * s for x in a)


def vkey(a: Vector):
    return tuple(reversed(a))


def in_h(a: Vector, n: int) -> bool:
    return all(x == 0 for x in a[n:])


def in_v_for_valuation(a: Vector, n: int) -> bool:
    """Exact coarsened nonnegativity, for a finite rank vector."""
    high = tuple(reversed(a[n:]))
    return high >= (F(0),) * len(high)


def in_q_for_valuation(a: Vector, n: int) -> bool:
    high = tuple(reversed(a[n:]))
    return high > (F(0),) * len(high)


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def require(self, condition: bool, category: str, context: str) -> None:
        if not condition:
            raise AssertionError(f"{category}: {context}")
        self.counts[category] += 1


def run() -> dict:
    checks = Checks()
    rng = random.Random(20260922)
    patterns = [
        [(F(1), 1)],
        [(F(1), 3)],
        [(F(1), 2), (F(2), 1)],
        [(F(-1), 2), (F(2), 2)],
        [(F(1), 1), (F(2), 2), (F(3), 1)],
        [(F(1), 3), (F(3, 2), 2)],
        [(F(-1), 1), (F(1), 2), (F(2), 3)],
        [(F(1), 2), (F(101, 100), 2)],
    ]
    past_nodes = [(F(0), 2), (F(1, 7), 1), (F(-2, 7), 2)]
    q = root_product(past_nodes)
    cases = 0
    for pattern in patterns:
        p = root_product(pattern)
        size = len(p) - 1
        for repetition in range(3):
            cases += 1
            context = f"case {cases}"
            data = [(x, [F(rng.randint(-9, 9), rng.randint(1, 7))
                         for _ in range(m)]) for x, m in pattern]
            delta = hermite(data)
            checks.require(len(delta) <= size, "Hermite degree bound", context)
            for x, jets in data:
                for order, expected in enumerate(jets):
                    checks.require(hasse(delta, x, order) == expected,
                                   "Hermite jet identity", context)
            for d in [0, 1, 2, 5, 11]:
                factor = mul(power(T, d), q)
                inverse = invmod(factor, p)
                checks.require(rem(mul(factor, inverse), p) == ONE,
                               "Finite quotient inverse", context)
                u = rem(mul(delta, inverse), p)
                correction = mul(factor, u)
                checks.require(len(u) <= size, "Inverse-jet degree bound", context)
                checks.require(rem(correction, p) == delta,
                               "Shell correction congruence", context)
                checks.require(all(c == 0 for c in correction[:d]),
                               "Correction low-degree vanishing", context)
                for x, m in past_nodes:
                    for order in range(m):
                        checks.require(hasse(correction, x, order) == 0,
                                       "Earlier-jet preservation", context)
                for x, jets in data:
                    for order, value in enumerate(jets):
                        checks.require(hasse(correction, x, order) == value,
                                       "Current-shell jet identity", context)
            # Includes both units and zero divisors in the determinant tests.
            for r in [delta, poly([-pattern[0][0], 1]), ONE, ZERO]:
                norm = determinant(multiplication_matrix(r, p))
                predicted = F(1)
                for x, m in pattern:
                    predicted *= evaluate(r, x) ** m
                checks.require(norm == predicted,
                               "Multiplication determinant formula", context)
                if predicted:
                    rinverse = invmod(r, p)
                    checks.require(rem(mul(r, rinverse), p) == ONE,
                                   "Nonzero-determinant inverse", context)
    # Finite coordinates in the largest-index ordering used in Gamma_infinity.
    rank = 12
    zero = (F(0),) * rank
    basis = [tuple(F(int(i == j)) for i in range(rank)) for j in range(rank)]
    for n in range(1, 11):
        rho, lam = basis[n - 1], basis[n]
        eps = vadd(lam, rho)
        checks.require(not in_v_for_valuation(vscale(eps, -1), n),
                       "Close-pair forbidden coefficient", f"shell {n}")
        checks.require(in_v_for_valuation(vadd(lam, vscale(eps, -1)), n),
                       "Close-pair corrected value", f"shell {n}")
        low = zero
        for j in range(n - 1):
            low = vadd(low, basis[j])
        displayed = vadd(vadd(lam, vscale(rho, 2 - n)), low)
        factorwise = vadd(lam, rho)
        for j in range(n - 1):
            factorwise = vadd(factorwise, vadd(basis[j], vscale(rho, -1)))
        checks.require(displayed == factorwise,
                       "Paired-root valuation formula", f"shell {n}")
        checks.require(in_q_for_valuation(displayed, n),
                       "Paired-root coarse maximal ideal", f"shell {n}")
        for m in [0, 1, 2, 10, 1000000]:
            val = vscale(rho, -m)
            checks.require(in_h(val, n) and in_v_for_valuation(val, n),
                           "Arbitrary finite-power scale", f"shell {n}, m={m}")
    # A finite elementary-symmetric minimum, with repeated radii.
    radii = [basis[0], basis[0], basis[1], basis[2], basis[2],
             basis[3], basis[4], basis[5], basis[6]]
    for length in range(1, len(radii) + 1):
        for degree in range(1, length + 1):
            sums: list[Vector] = []
            for indices in combinations(range(length), degree):
                total = zero
                for index in indices:
                    total = vadd(total, radii[index])
                sums.append(total)
            minimum = min(sums, key=vkey)
            predicted = zero
            for radius in radii[:degree]:
                predicted = vadd(predicted, radius)
            checks.require(minimum == predicted,
                           "Finite canonical-product minimum",
                           f"length {length}, degree {degree}")
            if degree >= 2:
                lhs = vscale(predicted, F(1, degree))
                rhs = vscale(radii[degree // 2 - 1], F(1, 2))
                checks.require(vkey(lhs) >= vkey(rhs),
                               "Product average lower bound",
                               f"length {length}, degree {degree}")
    return {
        "status": "passed",
        "arithmetic": "fractions.Fraction; no floating point",
        "random_seed": 20260922,
        "finite_polynomial_cases": cases,
        "damping_exponents_tested": [0, 1, 2, 5, 11],
        "rank_vector_dimension": rank,
        "checks_passed": sum(checks.counts.values()),
        "categories": dict(sorted(checks.counts.items())),
        "scope": "Finite identities and finite rank-vector calculations only.",
        "not_verified": [
            "Infinite strong summability or cofinality",
            "Existence or nonexistence of an infinite entire interpolant",
            "The infinite quotient or ultrafilter theorems",
            "Independent mathematical refereeing or Lean verification"
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New JSON output file (existing files are not overwritten)")
    args = parser.parse_args()
    if args.output.exists():
        parser.error(f"Refusing to overwrite existing file: {args.output}")
    if not args.output.parent.exists():
        parser.error(f"Output directory does not exist: {args.output.parent}")
    result = run()
    with args.output.open("x", encoding="utf-8") as out:
        json.dump(result, out, indent=2)
        out.write("\n")
    print(f"PASS: {result['checks_passed']} exact finite checks")
    print(f"Record: {args.output}")


if __name__ == "__main__":
    main()
