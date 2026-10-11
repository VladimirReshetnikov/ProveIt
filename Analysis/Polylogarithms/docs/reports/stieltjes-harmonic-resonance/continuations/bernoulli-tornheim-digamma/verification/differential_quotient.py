"""Exact research calculations for the differential-polynomial quotient.

X_j represents psi^(j-1), has weight j and factor degree one.
The canonical remainder retains partitions with repeated largest part.
This is an algebraic certificate; it does not certify arithmetic
independence of the resulting finite-part integrals.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

import sympy as sp

MAX_WEIGHT = 12
X = sp.symbols(f"X1:{MAX_WEIGHT + 2}")
gamma = sp.Symbol("gamma")
zetas = {j: sp.Symbol(f"z{j}") for j in range(2, MAX_WEIGHT + 2)}


def derivative(poly):
    return sp.expand(sum(sp.diff(poly, x) * X[j + 1]
                         for j, x in enumerate(X[:-1])))


def partition_of(exponents):
    return tuple(j + 1 for j in reversed(range(len(exponents)))
                 for _ in range(exponents[j]))


def monomial(partition):
    return sp.prod(X[j - 1] for j in partition)


def partitions(n, max_part=None):
    if n == 0:
        yield ()
        return
    for j in range(min(n, n if max_part is None else max_part), 0, -1):
        for rest in partitions(n - j, j):
            yield (j,) + rest


def normal_form(poly):
    """Return remainder R and primitive T with poly = R + D T."""
    remainder = sp.expand(poly)
    primitive = sp.Integer(0)
    while True:
        candidates = []
        for powers, coefficient in sp.Poly(remainder, *X).terms():
            part = partition_of(powers)
            if part and part[0] > 1 and part.count(part[0]) == 1:
                candidates.append((part, coefficient))
        if not candidates:
            break
        part, coefficient = max(candidates)
        predecessor = tuple(sorted((part[0] - 1,) + part[1:], reverse=True))
        multiplicity = predecessor.count(predecessor[0])
        step = coefficient * monomial(predecessor) / multiplicity
        primitive += step
        remainder = sp.expand(remainder - derivative(step))
    primitive = sp.expand(primitive)
    assert sp.expand(poly - remainder - derivative(primitive)) == 0
    return remainder, primitive


def endpoint(poly, weight):
    """F(1)-CT_{x=0}F from a finite Laurent truncation."""
    x = sp.Symbol("x")
    local = -1 / x - gamma + sum(
        (-1) ** j * zetas[j] * x ** (j - 1) for j in range(2, weight + 1))
    at_one = {X[0]: -gamma}
    at_one.update({X[j - 1]: (-1) ** j * sp.factorial(j - 1) * zetas[j]
                   for j in range(2, weight + 1)})
    one = sp.expand(poly.subs(at_one))
    constant = sp.expand(poly.subs(
        {X[j - 1]: sp.diff(local, x, j - 1)
         for j in range(1, weight + 1)})).coeff(x, 0)
    return tuple(sp.expand(v) for v in (one, constant, one - constant))


def serialize(poly):
    answer = []
    for powers, coefficient in sp.Poly(poly, *X).terms():
        if coefficient:
            answer.append({"partition": partition_of(powers),
                           "coefficient": str(coefficient)})
    return answer


def main():
    all_A = [sp.Integer(1)]
    tables = []
    for n in range(1, MAX_WEIGHT + 1):
        all_A.append(sp.expand(X[0] * all_A[-1] - derivative(all_A[-1])))
        remainder, primitive = normal_form(all_A[-1])
        assert sp.expand(remainder.subs({x: -x for x in X}) - (-1) ** n * remainder) == 0
        parts = list(partitions(n))
        repeated = [p for p in parts if len(p) > 1 and p[0] == p[1]]
        if n == 1:
            repeated = [(1,)]
        if n >= 2:
            assert len(repeated) == len(parts) - len(list(partitions(n - 1)))
        by_length = Counter(map(len, repeated))
        for length, dimension in by_length.items():
            expected = sum(len(p) == length for p in parts)
            expected -= sum(len(p) == length for p in partitions(n - 1))
            assert dimension == expected
        parity_basis = [p for p in repeated if len(p) % 2 == n % 2]
        # Complete spanning and independence gate: every monomial reduces;
        # total derivatives have zero remainder.
        for p in parts:
            reduced, antiderivative = normal_form(monomial(p))
            assert sp.expand(monomial(p) - reduced - derivative(antiderivative)) == 0
        if n >= 2:
            for p in partitions(n - 1):
                assert normal_form(derivative(monomial(p)))[0] == 0
        tables.append({"weight": n, "partition_count": len(parts),
                       "quotient_dimension": len(repeated),
                       "factor_dimensions": dict(sorted(by_length.items())),
                       "parity_dimension": len(parity_basis),
                       "basis": repeated, "parity_basis": parity_basis,
                       "A_normal": serialize(remainder),
                       "A_primitive": serialize(primitive)})

    sixth, H5 = normal_form(all_A[6])
    seventh, H6 = normal_form(all_A[7])
    assert sp.expand(sixth - (X[0] ** 6 - 15 * X[0] ** 2 * X[1] ** 2 + X[2] ** 2)) == 0
    endpoint_sixth = endpoint(H5, 5)
    endpoint_seventh = endpoint(H6, 6)

    # Gamma--Appell form using y = psi + gamma.  The central gamma
    # cancels, while the scalar coefficients retain zeta cumulants.
    centered = X[0] + gamma
    _, H3 = normal_form(all_A[4])
    _, H2 = normal_form(all_A[3])
    _, H1 = normal_form(all_A[2])
    _, H4 = normal_form(all_A[5])
    T5 = (H5 + 15 * zetas[2] * H3 + 40 * zetas[3] * H2
          + (45 * zetas[2] ** 2 + 90 * zetas[4]) * H1).subs(X[0], centered)
    T5 = sp.expand(T5)
    endpoint_appell = endpoint(T5, 5)
    assert sp.expand(endpoint_appell[2] + 60 * zetas[2] * zetas[3] + 242 * zetas[5]) == 0

    T6 = (H6 + 21 * zetas[2] * H4 + 70 * zetas[3] * H3
          + (105 * zetas[2] ** 2 + 210 * zetas[4]) * H2
          + (420 * zetas[2] * zetas[3] + 504 * zetas[5]) * H1).subs(X[0], centered)
    T6 = sp.expand(T6)
    endpoint_appell_seventh = endpoint(T6, 6)
    assert sp.expand(endpoint_appell_seventh[2]
                     + 448 * zetas[2] * zetas[4]
                     + 231 * zetas[3] ** 2 + 1596 * zetas[6]) == 0
    # zeta(2) zeta(4) = 7 zeta(6)/4 gives the printed final form.
    endpoint_appell_seventh_reduced = sp.expand(
        endpoint_appell_seventh[2].subs(zetas[2] * zetas[4],
                                       sp.Rational(7, 4) * zetas[6]))
    assert sp.expand(endpoint_appell_seventh_reduced
                     + 231 * zetas[3] ** 2 + 2380 * zetas[6]) == 0

    # The exact grouped subtraction for the one retained sixth moment.
    x = sp.Symbol("x")
    local_y = -1 / x + sum((-1) ** j * zetas[j] * x ** (j - 1)
                            for j in range(2, 7))
    local_mixed6 = sp.expand(local_y ** 2 * sp.diff(local_y, x) ** 2)
    mixed6_principal = sp.expand(sum(local_mixed6.coeff(x, -j) / x ** j
                                    for j in range(1, 7)))
    mixed6_principal_reduced = sp.expand(
        mixed6_principal.subs(zetas[2] ** 2, sp.Rational(5, 2) * zetas[4]))
    assert sp.expand(mixed6_principal_reduced - (x ** -6
                     - 2 * zetas[3] * x ** -3 - zetas[4] * x ** -2
                     + 6 * (zetas[2] * zetas[3] - zetas[5]) / x)) == 0

    # Independent product-rule check of the formal adjoint identity.
    # B_j(X)=Gamma^(-1) D^j Gamma=(-1)^j A_j(-X).
    neg = {x: -x for x in X}
    adjoint_checks = []
    for n in range(1, MAX_WEIGHT + 1):
        L = sum((-1) ** j * ((-1) ** j * all_A[j].subs(neg))
                * ((-1) ** (n - 1 - j) * all_A[n - 1 - j])
                for j in range(n))
        defect = sp.expand(derivative(L) - ((-1) ** n * all_A[n] - all_A[n].subs(neg)))
        assert defect == 0
        adjoint_checks.append(n)

    payload = {"status": "exact symbolic assertions passed", "max_weight": MAX_WEIGHT,
               "tables": tables, "adjoint_checks": adjoint_checks,
               "sixth": {"A": str(all_A[6]), "normal": str(sixth),
                         "primitive": str(H5),
                         "endpoint_at_one": str(endpoint_sixth[0]),
                         "endpoint_at_zero_CT": str(endpoint_sixth[1]),
                         "endpoint_difference": str(endpoint_sixth[2]),
                         "appell_primitive": str(T5),
                         "appell_endpoint_at_one": str(endpoint_appell[0]),
                         "appell_endpoint_at_zero_CT": str(endpoint_appell[1]),
                         "appell_endpoint": str(endpoint_appell[2]),
                         "mixed_principal_part": str(mixed6_principal_reduced)},
               "seventh": {"A": str(all_A[7]), "normal": str(seventh),
                           "primitive": str(H6),
                           "endpoint_at_one": str(endpoint_seventh[0]),
                           "endpoint_at_zero_CT": str(endpoint_seventh[1]),
                           "endpoint_difference": str(endpoint_seventh[2]),
                           "appell_primitive": str(T6),
                           "appell_endpoint_at_one": str(endpoint_appell_seventh[0]),
                           "appell_endpoint_at_zero_CT": str(endpoint_appell_seventh[1]),
                           "appell_endpoint": str(endpoint_appell_seventh[2]),
                           "appell_endpoint_reduced": str(endpoint_appell_seventh_reduced)}}
    output = Path(__file__).resolve().parent.parent / "results" / "differential_quotient.json"
    output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"output": str(output), "status": payload["status"],
                      "weights": MAX_WEIGHT,
                      "sixth_normal": str(sixth),
                      "sixth_endpoint": str(endpoint_sixth[2]),
                      "appell_endpoint": str(endpoint_appell[2]),
                      "seventh_normal": str(seventh),
                      "seventh_primitive": str(H6),
                      "seventh_endpoint": str(endpoint_seventh[2]),
                      "seventh_appell_endpoint": str(endpoint_appell_seventh_reduced),
                      "mixed6_principal": str(mixed6_principal_reduced),
                      "parity_counts": [t["parity_dimension"] for t in tables]}, indent=2))


if __name__ == "__main__":
    main()
