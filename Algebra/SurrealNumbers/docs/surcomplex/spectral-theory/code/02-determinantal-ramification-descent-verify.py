#!/usr/bin/env python3
"""Finite exact checks for the accompanying spectral-descent article.

Requires Python >= 3.9 and SymPy 1.14.0.  No numerical sampling is used.
These checks do not prove statements about arbitrary Hahn supports.
Run: python code/verify.py --output-dir /path/to/results
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
import random
import sys
import time
from collections import defaultdict
from pathlib import Path
from typing import Iterable, Optional, Sequence

import sympy as sp


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = defaultdict(int)
        self.notes: list[str] = []

    def equal(self, actual, expected, category: str, label: str) -> None:
        if isinstance(actual, sp.Basic) or isinstance(expected, sp.Basic):
            ok = sp.simplify(actual - expected) == 0
        else:
            ok = actual == expected
        if not ok:
            raise AssertionError(f"{category}: {label}\nactual={actual}\nexpected={expected}")
        self.counts[category] += 1

    def matrix(self, actual: sp.Matrix, expected: sp.Matrix, category: str, label: str) -> None:
        if actual.shape != expected.shape:
            raise AssertionError(f"Shape mismatch for {label}")
        for i in range(actual.rows):
            for j in range(actual.cols):
                self.equal(actual[i, j], expected[i, j], category, f"{label}[{i},{j}]")


def expand_matrix(a: sp.Matrix) -> sp.Matrix:
    return a.applyfunc(sp.expand)


def spectral_projector_checks(c: Checks, order: int = 6) -> None:
    """Exact truncated series, using the rational-residue path formula."""
    n = 3
    z = sp.zeros(n)
    identity = sp.eye(n)
    D = sp.diag(0, 0, 3)
    E = sp.Matrix([[1, 1, sp.I], [1, -1, 2], [-sp.I, 2, 0]])
    Q = sp.diag(1, 1, 0)
    Qc = identity - Q

    def const(a: sp.Matrix) -> list[sp.Matrix]:
        return [a] + [sp.zeros(n) for _ in range(order)]

    def add(a, b):
        return [expand_matrix(x + y) for x, y in zip(a, b)]

    def scale(a, scalar):
        return [expand_matrix(scalar * x) for x in a]

    def mul(a, b):
        return [expand_matrix(sum((a[j] * b[k-j] for j in range(k+1)), sp.zeros(n)))
                for k in range(order+1)]

    def star(a):
        return [expand_matrix(x.conjugate().T) for x in a]

    def equal_series(a, b, label):
        for k in range(order+1):
            c.matrix(a[k], b[k], "projector_and_polar_coefficients", f"{label}:t^{k}")

    # The term R0 (E R0)^k is a sum over paths of k transitions.
    # If a path visits the zero eigenspace a times and the 3 eigenspace b
    # times, its residue at zero is (-1)^b * binom(k-1,a-1) / 3^k.
    P = [Q]
    path_count = 0
    for k in range(1, order+1):
        pk = sp.zeros(n)
        for path in itertools.product(range(n), repeat=k+1):
            a = sum(index != 2 for index in path)
            b = k+1-a
            if a == 0 or b == 0:
                continue
            product = sp.Integer(1)
            for left, right in zip(path, path[1:]):
                product *= E[left, right]
            if product == 0:
                continue
            residue = sp.Rational((-1)**b, 3**k) * sp.binomial(k-1, a-1)
            pk[path[0], path[-1]] += residue * product
            path_count += 1
        P.append(expand_matrix(pk))

    one = const(identity)
    zero = const(z)
    Pc = add(one, scale(P, -1))
    B = const(D)
    B[1] = E
    equal_series(star(P), P, "P*=P")
    equal_series(mul(P, P), P, "P^2=P")
    equal_series(mul(P, Pc), zero, "P Pc=0")
    equal_series(mul(B, P), mul(P, B), "BP=PB")

    X = add(mul(P, const(Q)), mul(Pc, const(Qc)))
    G = mul(star(X), X)
    H = add(G, scale(one, -1))
    inverse_half = const(identity)
    power = const(identity)
    for j in range(1, order+1):
        power = mul(power, H)
        inverse_half = add(inverse_half, scale(power, sp.binomial(sp.Rational(-1, 2), j)))
    W = mul(X, inverse_half)
    equal_series(mul(star(W), W), one, "W*W=I")
    equal_series(mul(P, W), mul(W, const(Q)), "PW=WQ")
    transformed = mul(star(W), mul(B, W))
    for k in range(order+1):
        for i, j in [(0, 2), (1, 2), (2, 0), (2, 1)]:
            c.equal(transformed[k][i, j], 0, "block_and_low_degree_terms", f"offblock {k},{i},{j}")
    c.matrix(W[0], identity, "block_and_low_degree_terms", "W0")
    K = sp.zeros(n)
    for i in range(n):
        for j in range(n):
            if D[i, i] != D[j, j]:
                K[i, j] = E[i, j] / (D[j, j]-D[i, i])
    c.matrix(W[1], K, "block_and_low_degree_terms", "W1")
    expected_second = sp.zeros(n)
    for i in range(n):
        for j in range(n):
            if D[i, i] == D[j, j]:
                for ell in range(n):
                    if D[ell, ell] != D[i, i]:
                        expected_second[i, j] += E[i, ell] * E[ell, j] / (D[i, i]-D[ell, ell])
    c.matrix(transformed[2], expected_second, "block_and_low_degree_terms", "second-order blocks")
    c.notes.append(f"3x3 Hermitian projector and polar identities checked through degree {order}; "
                   f"{path_count} nonzero residue-path contributions evaluated.")


def displayed_example_checks(c: Checks) -> None:
    t, u, s = sp.symbols("t u s", positive=True)
    a, b, X = sp.symbols("a b X")
    A = sp.Matrix([[t**3, t**4], [t**4, 0]])
    root = sp.sqrt(1+4*t*t)
    lp, lm = t**3*(1+root)/2, t**3*(1-root)/2
    c.equal(lp*lp-t**3*lp-t**8, 0, "displayed_identities", "positive branch characteristic")
    c.equal(lm*lm-t**3*lm-t**8, 0, "displayed_identities", "negative branch characteristic")
    w = (root-1)/(2*t)
    c.equal(t*w*w+w-t, 0, "displayed_identities", "eigenvector slope equation")
    U = sp.Matrix([[1, -w], [w, 1]]) / sp.sqrt(1+w*w)
    c.matrix(U.T*U, sp.eye(2), "displayed_identities", "2x2 unitary")
    c.matrix(U.T*A*U, sp.diag(lp, lm), "displayed_identities", "2x2 diagonalization")
    expected_lp = t**3+t**5-t**7+2*t**9-5*t**11+14*t**13-42*t**15
    c.equal(sp.series(lp, t, 0, 17).removeO(), expected_lp, "displayed_identities", "lambda-plus coefficients")
    c.equal(sp.series(lm, t, 0, 17).removeO(), t**3-expected_lp, "displayed_identities", "lambda-minus coefficients")
    c.equal(sp.series(w, t, 0, 11).removeO(), t-t**3+2*t**5-5*t**7+14*t**9,
            "displayed_identities", "slope coefficients")

    L = t*(1-sp.sqrt(1+4*u*u/(t*t)))/2
    c.equal(L*L-t*L-u*u, 0, "displayed_identities", "rank-two characteristic")
    expected_L = -u*u/t + u**4/t**3 - 2*u**6/t**5 + 5*u**8/t**7
    c.equal(sp.series(L, u, 0, 10).removeO(), expected_L, "displayed_identities", "rank-two expansion")

    A2 = sp.Matrix([[1+s*s, 1], [1, 1]])
    N = A2+s*sp.eye(2)
    d2 = 2+s*s+2*s
    c.matrix(N*N, d2*A2, "displayed_identities", "principal square-root numerator")
    c.equal(sp.trace(N), d2, "displayed_identities", "trace numerator")
    c.equal((d2-2-s*s)/2, s, "displayed_identities", "recover fractional monomial from trace")

    gram_witness = sp.Matrix([[t, 1], [0, u]])
    gram = sp.Matrix([[t*t, t], [t, 1+u*u]])
    c.matrix(gram_witness.T*gram_witness, gram, "displayed_identities", "Gram product")
    c.equal(gram.det(), t*t*u*u, "displayed_identities", "Gram determinant")
    orbit_polynomial = sp.prod(X-eps*a-eta*b for eps in (-1, 1) for eta in (-1, 1))
    expected = X**4-2*(a*a+b*b)*X*X+(a*a-b*b)**2
    c.equal(sp.expand(orbit_polynomial), expected, "displayed_identities", "biquadratic trace orbit")
    c.equal(len({(eps, eta) for eps in (-1, 1) for eta in (-1, 1)}), 4,
            "displayed_identities", "distinct formal coset conjugates")
    c.notes.append("All displayed spectral expansions, principal-root numerator, Gram product, "
                   "and biquadratic trace polynomial checked exactly.")


def subgroup(generators: Sequence[Sequence[int]], q: int, dimension: int) -> set[tuple[int, ...]]:
    zero = (0,)*dimension
    elements = {zero}
    for generator in generators:
        old = list(elements)
        elements = {
            tuple((x[j]+k*generator[j]) % q for j in range(dimension))
            for x in old for k in range(q)
        }
    return elements


def int_det(matrix: Sequence[Sequence[int]]) -> int:
    n = len(matrix)
    if n == 0:
        return 1
    if n == 1:
        return matrix[0][0]
    return sum((-1)**j * matrix[0][j] * int_det([list(row[:j])+list(row[j+1:])
                                               for row in matrix[1:]]) for j in range(n))


def quotient_checks(c: Checks) -> list[dict]:
    rng = random.Random(20260921)
    records = []
    for d in (1, 2, 3):
        for q in (2, 3, 4, 6):
            for r in (1, 2, 3, 4):
                gammas = [tuple(rng.randint(-3, 5) for _ in range(d)) for _ in range(r)]
                delta = []
                running = (0,)*d
                for gamma in gammas:
                    running = tuple(x+y for x, y in zip(running, gamma))
                    delta.append(running)
                G = subgroup(gammas, q, d)
                R = subgroup(delta, q, d)
                c.equal(G, R, "finite_ramification_groups", f"partial-sum generators {d},{q},{r}")
                columns = [tuple(q if i == j else 0 for i in range(d)) for j in range(d)] + delta
                gcd = 0
                for choices in itertools.combinations(range(len(columns)), d):
                    matrix = [[columns[j][i] for j in choices] for i in range(d)]
                    gcd = math.gcd(gcd, abs(int_det(matrix)))
                c.equal(q**d // gcd, len(G), "finite_ramification_groups", f"minor-index degree {d},{q},{r}")
                c.equal(len(G) <= q**r, True, "finite_ramification_groups", f"degree bound {d},{q},{r}")
                # Characters of the ambient group restricted to G, represented by
                # exponents modulo q, require no approximate roots of unity.
                ordered_G = sorted(G)
                restrictions = {
                    tuple(sum(m[j]*h[j] for j in range(d)) % q for h in ordered_G)
                    for m in itertools.product(range(q), repeat=d)
                }
                c.equal(len(restrictions), len(G), "finite_character_checks", f"dual cardinality {d},{q},{r}")
                positions = {h: i for i, h in enumerate(ordered_G)}
                occupied = {tuple(x % q for x in gamma) for gamma in gammas}
                stabilizer = [character for character in restrictions
                              if all(character[positions[h]] == 0 for h in occupied)]
                c.equal(len(stabilizer), 1, "finite_character_checks", f"positive coset stabilizer {d},{q},{r}")
                records.append({"dimension": d, "q": q, "number_of_generators": r,
                                "eigenvalue_valuations": gammas, "minor_valuations": delta,
                                "degree": len(G), "lattice_index": gcd})
    c.notes.append(f"{len(records)} finite quotient cases checked by subgroup enumeration, "
                   "maximal integer minors, and exact character restrictions.")
    return records


def rational_valuation(expr, t, u) -> Optional[tuple[int, int]]:
    """v(t)=(0,1), v(u)=(1,0), ordered lexicographically; None means infinity."""
    expr = sp.cancel(expr)
    if expr == 0:
        return None
    numerator, denominator = sp.fraction(expr)
    def polynomial_value(p) -> tuple[int, int]:
        # variables ordered u,t so exponent tuples already have valuation order
        poly = sp.Poly(p, u, t, extension=sp.I)
        return min(monomial for monomial, coefficient in poly.terms() if coefficient != 0)
    vnum, vden = polynomial_value(numerator), polynomial_value(denominator)
    return (vnum[0]-vden[0], vnum[1]-vden[1])


def matrix_profile_checks(c: Checks) -> list[dict]:
    t, u = sp.symbols("t u", positive=True)
    def rotation(variable, i, j):
        R = sp.eye(3)
        R[i, i] = R[j, j] = (1-variable**2)/(1+variable**2)
        R[i, j] = -2*variable/(1+variable**2)
        R[j, i] = 2*variable/(1+variable**2)
        return R
    U = rotation(t, 0, 1)*rotation(u, 1, 2)
    c.matrix(U.T*U, sp.eye(3), "rational_matrix_profiles", "rational orthogonal basis")
    profiles = [
        [(0, 0), (0, 2), (2, 1)],
        [(-1, 3), (0, 0), (1, -2)],
        [(0, 1), (1, 0), None],
        [None, (1, 2), None],
        [(0, 0), (0, 0), (0, 0)],
        [(0, 2), (0, 4), (2, 2)],
    ]
    records = []
    for case, gammas in enumerate(profiles):
        diagonal = [0 if gamma is None else u**gamma[0]*t**gamma[1]*(1+(j+1)*t)
                    for j, gamma in enumerate(gammas)]
        A = (U*sp.diag(*diagonal)*U.T).applyfunc(sp.cancel)
        c.matrix(A.T, A, "rational_matrix_profiles", f"case {case} symmetry")
        expected_values = sorted(gamma for gamma in gammas if gamma is not None)
        delta = []
        running = (0, 0)
        for k in range(1, 4):
            values = []
            for I in itertools.combinations(range(3), k):
                for J in itertools.combinations(range(3), k):
                    value = rational_valuation(A.extract(I, J).det(), t, u)
                    if value is not None:
                        values.append(value)
            actual = min(values) if values else None
            if k <= len(expected_values):
                running = tuple(a+b for a, b in zip(running, expected_values[k-1]))
                expected = running
                delta.append(actual)
            else:
                expected = None
            c.equal(actual, expected, "rational_matrix_profiles", f"case {case} Delta_{k}")
        degrees = {}
        for q in (2, 3, 4, 6):
            degree_from_minors = len(subgroup(delta, q, 2))
            degree_from_spectrum = len(subgroup(expected_values, q, 2))
            c.equal(degree_from_minors, degree_from_spectrum, "rational_matrix_profiles", f"case {case} q={q}")
            degrees[str(q)] = degree_from_minors
        records.append({"case": case, "eigenvalue_valuations": gammas,
                        "minor_valuations": delta, "root_extension_degrees": degrees})
    c.notes.append(f"{len(profiles)} rational 3x3 positive-semidefinite matrix profiles checked "
                   "by enumerating every minor, including rank-deficient cases.")
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parents[1]/"data")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    c = Checks()
    spectral_projector_checks(c)
    displayed_example_checks(c)
    quotient_records = quotient_checks(c)
    profiles = matrix_profile_checks(c)
    report = {
        "status": "PASS",
        "total_scalar_assertions": sum(c.counts.values()),
        "assertions_by_category": dict(c.counts),
        "notes": c.notes,
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "platform": platform.platform(),
        "seed": 20260921,
        "elapsed_seconds": round(time.monotonic()-start, 3),
        "formal_projector_truncation_degree": 6,
        "finite_quotient_cases": quotient_records,
        "rational_matrix_profiles": profiles,
        "limitations": [
            "Finite identities and examples only; no proof-assistant verification.",
            "No exhaustive computation over arbitrary Hahn supports or ordered groups.",
            "The general support and field-theoretic results require the proofs in article.tex.",
            "Scalar coefficient assertions are counted separately, including zero coefficients."
        ],
    }
    (args.output_dir/"verification.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    text = ["PASS", f"Total exact scalar assertions: {report['total_scalar_assertions']}",
            f"Python {report['python']}; SymPy {report['sympy']}",
            f"Elapsed seconds: {report['elapsed_seconds']}", "", "Categories:"]
    text.extend(f"  {category}: {count}" for category, count in sorted(c.counts.items()))
    text += ["", "Checks:"] + ["  "+note for note in c.notes]
    text += ["", "Limits:"] + ["  "+note for note in report["limitations"]]
    output = "\n".join(text)+"\n"
    (args.output_dir/"verification.txt").write_text(output, encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
