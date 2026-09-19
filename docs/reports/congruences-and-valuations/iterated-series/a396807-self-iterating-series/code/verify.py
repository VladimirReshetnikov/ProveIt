#!/usr/bin/env python3
"""Reproduce the exact-arithmetic checks and data files in the report.

Run: python code/verify.py
Only the Python standard library is required.  This is a finite verification
suite, not a substitute for the all-degree proofs in article.tex.
"""
from __future__ import annotations
import json
import platform
import time
from math import gcd, factorial, comb
from pathlib import Path
from series_tools import (solve, multiply, compose, inverse, iterate,
                          correction_coefficients, last_two_digits)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)
PUBLISHED_PREFIX = [1, 1, 11, 201, 4721, 129671, 3976201, 132554541,
    4724742051, 178052854981, 7038323735281, 290148008603631,
    12419333556374881, 550091361259038561, 25145997103468438771,
    1183773515790240935841, 57289367885575671008761,
    2846138707414273744227111, 144972933910530413441182881]


def field_power(n: int) -> list[int]:
    """t^n mod (t^5-t+2) over F_5, ascending coefficient order."""
    def mul(a, b):
        c = [0] * 9
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                c[i+j] = (c[i+j] + ai*bj) % 5
        for i in range(8, 4, -1):
            c[i-4] = (c[i-4] + c[i]) % 5
            c[i-5] = (c[i-5] - 2*c[i]) % 5
        return c[:5]
    result, base = [1,0,0,0,0], [0,1,0,0,0]
    while n:
        if n & 1:
            result = mul(result, base)
        base = mul(base, base)
        n >>= 1
    return result


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    started = time.perf_counter()
    report = {"python": platform.python_version(), "arithmetic": "exact integers",
              "source_prefix": "OEIS A396807, retrieved 2026-09-19"}
    t = time.perf_counter()
    a = solve(5, 6, 400)
    report["exact_generation_seconds"] = round(time.perf_counter()-t, 6)
    require(a[1:20] == PUBLISHED_PREFIX, "published prefix differs")
    report["published_prefix_matched"] = 19
    report["exact_coefficients_generated"] = 400
    report["a400_decimal_digits"] = len(str(a[400]))
    h2, h5 = correction_coefficients(400)
    digits = last_two_digits(400)
    for n in range(1, 401):
        require(a[n] % 10 == 1, f"mod10 at {n}")
        require((a[n]-1-2*h2[n]) % 4 == 0, f"mod4 at {n}")
        require((a[n]-1-5*h5[n]) % 25 == 0, f"mod25 at {n}")
        require((a[n]-1-10*int(n % 3 == 0)) % 20 == 0, f"mod20 at {n}")
        require(a[n] % 100 == digits[n], f"mod100 at {n}")
    report["special_congruence_coefficient_checks"] = 2000
    for m in range(1, 201):
        require(a[2*m] >= 2**(m-1)*factorial(m-1), "even growth bound")
    report["even_growth_bound_checks"] = 200
    # Independent Horner composition: do not reuse substitution tables.
    n = 100
    f = a[:n+1]
    r5 = iterate(f, 5, n)
    r6 = iterate(f, 6, n)
    rhs = multiply(r5, r6, n)
    rhs[1] += 1
    require(rhs == f, "independent exact functional equation fails")
    report["independent_horner_equation_degree"] = n
    # Check negative as well as positive iterates. Cache the inverse once.
    n = 48
    f = a[:n+1]
    g = inverse(f, n, 10)
    identity = [0,1] + [0]*(n-1)
    require(compose(f, g, n, 10) == identity, "right inverse")
    require(compose(g, f, n, 10) == identity, "left inverse")
    for k in range(-20, 21):
        actual = iterate(g if k < 0 else f, abs(k), n, 10)
        expected = [0] + [pow(k, j-1, 10) for j in range(1, n+1)]
        require(actual == expected, f"iterate congruence k={k}")
    report["integer_iterate_coefficient_checks"] = 41*n
    # Universal weighted sharp-modulus and scaling checks.
    cases = 0
    for r in range(13):
        for s in range(13):
            unweighted = solve(r, s, 30)
            for c in (-3, -1, 0, 1, 2, 5):
                f = solve(r, s, 30, c)
                expected_gcd = gcd(c*c*(r+s-1), c**3*r*s)
                actual_gcd = 0
                for j in range(2, 31):
                    actual_gcd = gcd(actual_gcd, f[j]-c**(j-1))
                    require(f[j] == c**(j-1)*unweighted[j], "weighted scaling")
                require(actual_gcd == expected_gcd,
                        f"sharp gcd ({r},{s},{c})")
                cases += 1
    report["weighted_family_parameter_cases"] = cases
    report["weighted_family_coefficient_checks"] = cases*29
    # Exact compositional order modulo p^e: identity upper bound;
    # coefficient x^2 supplies the lower bound in the proof.
    order_cases = []
    for p in (2,5):
        for e in range(1,5):
            m = p**e
            actual = iterate(a[:41], m, 40, m)
            require(actual == [0,1]+[0]*39, f"order modulo {m}")
            order_cases.append(m)
    report["compositional_order_moduli_checked_to_degree_40"] = order_cases
    # Neighboring entry A396798, including all residue classes of the iterate.
    b = solve(4,5,100)
    for j in range(1,101):
        hc = comb(j-2,2) if j >= 4 else 0
        require((b[j]-1-4*hc) % 8 == 0, f"neighbor coefficients {j}")
    for k in range(1,9):
        bk = iterate(b[:61],k,60,8)
        for j in range(1,61):
            hc = comb(j-2,2) if j >= 4 else 0
            expected = (pow(k,j-1,8)+4*(k%2)*hc) % 8
            require(bk[j] == expected, f"neighbor iterate {k}, {j}")
    report["A396798_coefficient_checks"] = 100+8*60
    # A396797 is another exact-modulus specialization.
    b34 = solve(3,4,100)
    require(all(x % 6 == 1 for x in b34[1:]), "neighbor mod6")
    report["A396797_coefficient_checks"] = 100
    # Two full periods from the proven rational formula, not an independent
    # direct generation of 93720 enormous integer coefficients.
    period = 46860
    residues = last_two_digits(2*period)
    require(residues[1:period+1] == residues[period+1:2*period+1], "period")
    witnesses = {}
    for q in (2,3,5,11,71):
        shift = period//q
        witness = next((i for i in range(1,period+1)
                        if residues[i] != residues[i+shift]), None)
        require(witness is not None, f"smaller divisor-period {shift}")
        witnesses[str(shift)] = {"n": witness, "value": residues[witness],
                                "shifted_value": residues[witness+shift]}
    report["period_mod100"] = period
    report["rational_formula_residues_generated"] = 2*period
    report["proper_divisor_period_witnesses"] = witnesses
    powers = {str(k):field_power(k) for k in (3124,1562,284,44,781)}
    require(powers["3124"] == [1,0,0,0,0], "field order upper bound")
    require(all(powers[str(k)] != [1,0,0,0,0] for k in (1562,284,44)),
            "field order lower bound")
    report["finite_field_order_certificate"] = powers
    (DATA/"a396807_exact_400.txt").write_text(
        "# Independently generated with code/series_tools.py\n"
        "# n a(n), for 1 <= n <= 400\n" +
        "".join(f"{i} {a[i]}\n" for i in range(1,401)))
    (DATA/"a396807_mod100_period.txt").write_text(
        "# One complete minimal period, indexed from n=1.\n" +
        "".join(f"{i} {residues[i]:02d}\n" for i in range(1,period+1)))
    report["elapsed_seconds"] = round(time.perf_counter()-started, 6)
    report["status"] = "ALL CHECKS PASSED"
    (DATA/"verification.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
