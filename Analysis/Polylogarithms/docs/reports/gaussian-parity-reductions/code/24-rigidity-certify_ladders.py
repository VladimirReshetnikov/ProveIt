#!/usr/bin/env python3
"""Exact replay for complementary-power rigidity and plastic ladders.

The all-exponent classification is proved in article/sections/ladders.tex.
The finite polynomial survey here is a separate consistency check, not a
replacement for the cited Ljunggren--Tverberg irreducibility theorem.

Run: python certify_ladders.py --bound 30 --degree-limit 12 --out results
Dependencies: sympy; mpmath is used only for numerical sanity checks.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import defaultdict
from pathlib import Path

import mpmath as mp
import sympy as sp


X = sp.Symbol("X")
Q = sp.Rational
PLASTIC = sp.Poly(X**3 + X**2 - 1, X, domain=sp.QQ)
CHECKS = []


def require(test, name):
    if not bool(test):
        raise ArithmeticError(name)
    CHECKS.append(name)


def as_json(value):
    if isinstance(value, dict):
        return {str(k): as_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [as_json(v) for v in value]
    if isinstance(value, sp.Basic):
        return str(value)
    return value


def field_equal(lhs, rhs, name):
    """Check equality in Q[X]/(X^3+X^2-1), with nonzero denominator."""
    num, den = sp.fraction(sp.cancel(lhs - rhs))
    nr = sp.rem(num, PLASTIC.as_expr(), X)
    dr = sp.rem(den, PLASTIC.as_expr(), X)
    require(dr != 0 and nr == 0, name)
    return {"lhs": str(lhs), "rhs": str(rhs),
            "numerator_remainder": str(nr),
            "denominator_remainder": str(dr)}


def add_rows(*terms):
    out = defaultdict(lambda: Q(0))
    for coefficient, row in terms:
        for key, value in row.items():
            out[key] += coefficient * value
    return {k: sp.cancel(v) for k, v in out.items() if v}


def expand_modified(sign, exponent, coefficient=1):
    """P3 inversion and duplication; key 0 means zeta(3)=P3(1)."""
    exponent = abs(exponent)
    if sign == 1:
        return {exponent: Q(coefficient)}
    return add_rows((1, {exponent: -Q(coefficient)}),
                    (1, {2 * exponent: Q(coefficient, 4)}))


def plastic_certificates():
    complements = [(1, 5), (2, 3), (3, 2), (5, 1)]
    factorizations = [field_equal(1 - X**a, X**b,
                                   f"complement {a},{b}")
                      for a, b in complements]
    xx, yy = X, X**2
    rogers = [xx * yy, xx * (1 - yy) / (1 - xx * yy),
              yy * (1 - xx) / (1 - xx * yy)]
    rogers_powers = [3, 2, 5]
    rogers_certificates = [field_equal(lhs, X**power,
                                      f"Rogers argument {i+1}")
                           for i, (lhs, power) in
                           enumerate(zip(rogers, rogers_powers))]
    args = [xx, yy, xx * (1 - yy) / (xx - 1),
            yy * (1 - xx) / (yy - 1), (1 - xx) / (1 - yy),
            xx * (1 - yy) / (yy * (1 - xx)), xx * yy, xx / yy,
            xx * (1 - yy)**2 / (yy * (1 - xx)**2)]
    signed = [(1, 1), (1, 2), (-1, -1), (-1, 4), (1, 2),
              (1, -3), (1, 3), (1, -1), (1, -5)]
    kummer_certificates = [field_equal(lhs, sign * X**power,
                                      f"Kummer argument {i+1}")
                           for i, (lhs, (sign, power)) in
                           enumerate(zip(args, signed))]

    K = add_rows(*[(1, expand_modified(sign, power, coefficient))
                   for (sign, power), coefficient in
                   zip(signed, [2] * 6 + [-1] * 3)])
    expected_K = {1: -1, 2: Q(9, 2), 3: 1, 4: -2,
                  5: -1, 8: Q(1, 2)}
    require(K == expected_K, "Kummer row after inversion and duplication")
    A = {1: 1, 5: 1, 4: -1, 8: Q(1, 4)}
    target = {1: -1, 2: Q(3, 2), 3: Q(1, 3), 5: -1}
    reduced = add_rows((Q(1, 3), K), (Q(-2, 3), A))
    require(reduced == target, "plastic P3 target from (K-2A)/3")
    require(Q(1, 3) * 2 + Q(-2, 3) == 0,
            "plastic P3 zeta constant cancels")

    # Polynomial symbols stand for dilogarithms, zeta(2), and lambda^2.
    D1, D2, D3, D5, Z2, T2 = sp.symbols("D1 D2 D3 D5 Z2 T2")
    reflections = [D1 + D5 - Z2 + 5*T2,
                   D2 + D3 - Z2 + 6*T2]
    small = Q(1, 2)*D2 - D5 - T2
    S = -D1 + 3*D2 + D3 - 5*D5
    require(sp.expand(-reflections[0] + reflections[1] + 4*small
                      - (S - 3*T2)) == 0,
            "dilogarithm-tail certificate S=3 lambda^2")
    T_coefficient = sum(target[a] * a*a * b for a, b in complements)
    require(T_coefficient == -6, "logarithmic tail T=-6 lambda")
    require(-3 - Q(1, 3)*T_coefficient == -1,
            "P3 correction is minus lambda^3")

    B = {2: Q(5, 4), 3: 1, 1: -1}
    logfree3 = add_rows((8, A), (-4, B))
    expected_logfree3 = {1: 12, 2: -5, 3: -4, 4: -8, 5: 8, 8: 2}
    require(logfree3 == expected_logfree3,
            "log-free Li3 coefficient row 4(2A-B)")
    # Tail coordinate order: zeta(3), zeta(2)*lambda, lambda^3.
    tail_A = sp.Matrix([1, 1, Q(-7, 3)])
    tail_B = sp.Matrix([1, 2, Q(-14, 3)])
    require(8*tail_A - 4*tail_B == sp.Matrix([4, 0, 0]),
            "both ordinary Li3 logarithmic tails cancel")
    logfree2 = {1: 6, 2: -5, 3: -5, 5: 6}
    require(sp.expand(6*reflections[0]-5*reflections[1]
                      -(6*D1-5*D2-5*D3+6*D5-Z2)) == 0,
            "log-free Li2 coefficient row 6 reflection1-5 reflection2")

    # Explicit signed-unit orbits, checked in the number field.
    orbits = []
    for a, b in [(1, 5), (2, 3)]:
        orbit = [(1, a), (1, b), (1, -a), (1, -b),
                 (-1, b-a), (-1, a-b)]
        require(len(set(orbit)) == 6, f"six distinct orbit symbols {a},{b}")
        expressions = [sign * X**power for sign, power in orbit]
        for i, expr in enumerate(expressions):
            complement = next((z for z in expressions
                               if sp.rem(sp.fraction(sp.cancel(1-expr-z))[0],
                                         PLASTIC.as_expr(), X) == 0), None)
            require(complement is not None, f"orbit complement {a},{b},{i}")
            field_equal(1-expr, complement, f"orbit exact complement {a},{b},{i}")
        orbits.append(orbit)
    require(set(orbits[0]).isdisjoint(orbits[1]), "plastic orbits disjoint")

    return {"defining_polynomial": str(PLASTIC.as_expr()),
            "complement_factorizations": factorizations,
            "Rogers_arguments": rogers_certificates,
            "Kummer_arguments": kummer_certificates,
            "Kummer_signed_exponents": signed,
            "Kummer_row": K, "Landen_A_row": A,
            "P3_target": target, "row_operation": ["1/3", "-2/3"],
            "Li3_logfree_row": logfree3, "Li2_logfree_row": logfree2,
            "signed_orbits": orbits}


def trinomial_survey(bound, degree_limit):
    groups = defaultdict(list)
    data = []
    for b in range(2, bound + 1):
        for a in range(1, b):
            d = math.gcd(a, b)
            exceptional = (a//d % 6, b//d % 6) in {(1, 5), (5, 1)}
            f = sp.Poly(X**b + X**a - 1, X, domain=sp.QQ)
            c = sp.Poly(X**(2*d) - X**d + 1 if exceptional else 1,
                        X, domain=sp.QQ)
            h, remainder = f.div(c)
            require(remainder.is_zero, f"cyclotomic division {a},{b}")
            require(h.is_irreducible, f"exact quotient irreducibility {a},{b}")
            require(h.degree() == b - (2*d if exceptional else 0),
                    f"minimal degree {a},{b}")
            require(all(exponent[0] % d == 0 for exponent in h.monoms()),
                    f"root rotation support {a},{b}")
            key = tuple(h.all_coeffs())
            groups[key].append((a, b))
            data.append({"a": a, "b": b, "gcd": d,
                         "degree": h.degree(), "exceptional": exceptional,
                         "minimal_polynomial": str(h.as_expr())})
    collisions = [pairs for pairs in groups.values() if len(pairs) > 1]
    expected = [[(d, 5*d), (2*d, 3*d)] for d in range(1, bound//5 + 1)]
    canonical = lambda rows: sorted(sorted(row) for row in rows)
    require(canonical(collisions) == canonical(expected),
            "all finite collisions precisely scaled plastic pairs")
    # Check equal-pair irreducibility separately.
    for a in range(1, min(bound, degree_limit) + 1):
        require(sp.Poly(2*X**a-1, X, domain=sp.QQ).is_irreducible,
                f"equal pair reciprocal-Eisenstein {a}")

    complete_bound = (5*degree_limit)//3
    require(bound >= complete_bound, "survey covers degree completeness bound")
    bounded = [record for record in data if record["degree"] <= degree_limit]
    bounded_unique = {}
    for record in bounded:
        bounded_unique.setdefault(record["minimal_polynomial"], []).append(
            [record["a"], record["b"]])
    degree_counts = []
    for D in range(1, degree_limit + 1):
        selected = {r["minimal_polynomial"] for r in data if r["degree"] <= D}
        primitive = {r["minimal_polynomial"] for r in data
                     if r["degree"] <= D and r["gcd"] == 1}
        degree_counts.append({"degree_at_most": D,
                              "unequal_bases": len(selected),
                              "primitive_unequal_bases": len(primitive),
                              "equal_pair_bases": D,
                              "all_bases": len(selected)+D})
    return {"exponent_bound": bound,
            "trinomial_count": len(data),
            "exact_quotient_irreducibility_checks": len(data),
            "distinct_noncyclotomic_polynomials": len(groups),
            "collision_groups": canonical(collisions),
            "degree_limit": degree_limit,
            "proved_complete_exponent_bound": complete_bound,
            "degree_counts": degree_counts,
            "bounded_degree_polynomials": bounded_unique,
            "all_polynomials": data}


def numerical_checks():
    mp.mp.dps = 120
    q = mp.findroot(lambda t: t**3+t**2-1, (mp.mpf(".7"), mp.mpf(".8")))
    lam = mp.log(q)
    L = lambda s, k: mp.polylog(s, q**k)
    residuals = {
        "plastic_dilog": L(2, 2)/2-L(2, 5)-lam**2,
        "plastic_trilog": -L(3, 1)+mp.mpf(3)/2*L(3, 2)
                          +L(3, 3)/3-L(3, 5)-lam**3,
        "logfree_dilog": 6*L(2, 1)-5*L(2, 2)-5*L(2, 3)
                          +6*L(2, 5)-mp.zeta(2),
        "logfree_trilog": 12*L(3, 1)-5*L(3, 2)-4*L(3, 3)-8*L(3, 4)
                           +8*L(3, 5)+2*L(3, 8)-4*mp.zeta(3),
    }
    for name, value in residuals.items():
        require(abs(value) < mp.mpf("1e-110"), f"120-digit sanity {name}")
    return {"precision_decimal_digits": mp.mp.dps,
            "root": mp.nstr(q, 122),
            "residuals": {k: mp.nstr(v, 16) for k, v in residuals.items()},
            "status": "sanity checks; not proof certificates"}


def counting_certificates(max_degree=100):
    """Compare divisor counts, the theorem formula, and direct exponent sets."""
    e = {n: sum(math.gcd(a, n) == 1 and
                (a % 6, n % 6) in {(1, 5), (5, 1)}
                for a in range(1, n))
         for n in range(1, max_degree+3)}
    for n, value in e.items():
        via_mobius = (sum(int(sp.mobius(d))*((n//d+1)//6)
                          for d in sp.divisors(n))
                      if math.gcd(n, 6) == 1 else 0)
        require(value == via_mobius, f"exception count Mobius formula {n}")
    counts = []
    for D in range(1, max_degree+1):
        formula = D*(D+1)//2 - D//3
        formula += sum(e[D//d+1]+e[D//d+2] for d in range(1, D//3+1))
        canonical_seeds = set()
        for b in range(2, (5*D)//3+1):
            for a in range(1, b):
                d = math.gcd(a, b)
                aa, bb = a//d, b//d
                exc = (aa % 6, bb % 6) in {(1, 5), (5, 1)}
                degree = b - (2*d if exc else 0)
                if degree <= D:
                    key = (d, 2, 3) if (aa, bb) == (1, 5) else (d, aa, bb)
                    canonical_seeds.add(key)
        direct = len(canonical_seeds)+D
        require(formula == direct, f"exact base count formula degree {D}")
        counts.append({"degree_at_most": D, "number_of_bases": formula})
    return {"max_degree": max_degree, "e_values": e, "base_counts": counts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=30)
    parser.add_argument("--degree-limit", type=int, default=12)
    parser.add_argument("--out", type=Path, default=Path("results"))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    plastic = plastic_certificates()
    survey = trinomial_survey(args.bound, args.degree_limit)
    counting = counting_certificates()
    numeric = numerical_checks()
    report = {"status": "all checks passed", "check_count": len(CHECKS),
              "checks": CHECKS, "sympy_version": sp.__version__,
              "mpmath_version": mp.__version__,
              "plastic_certificates": plastic,
              "trinomial_survey": survey, "counting_certificates": counting,
              "numerical_checks": numeric}
    (args.out/"ladder_certificates.json").write_text(
        json.dumps(as_json(report), indent=2)+"\n", encoding="utf-8")
    rows = survey["degree_counts"]
    with (args.out/"degree_counts.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({"status": report["status"],
                      "check_count": report["check_count"],
                      "trinomial_count": survey["trinomial_count"],
                      "collision_groups": survey["collision_groups"],
                      "degree_counts": rows,
                      "numerical_residuals": numeric["residuals"]}, indent=2))


if __name__ == "__main__":
    main()
