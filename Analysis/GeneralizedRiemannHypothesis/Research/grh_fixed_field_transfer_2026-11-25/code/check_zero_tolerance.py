#!/usr/bin/env python3
"""Exact independent finite checks for the zero-tolerance shell-cost theorem.

The theorem itself is proved in the accompanying manuscript. These checks:
  * derive shell costs by exhaustive finite-field polynomials and packet cover DP;
  * check shifted cyclotomic polynomials and their strict Newton inequalities;
  * construct explicit binomial obstructions and certify all conjugate values
    through two exact resultants and their Newton polygons;
  * compare the old ramification bound with the exact budget-crossing cutoff.

Only Python's standard library and SymPy are needed. No network access.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import json
import sympy as sp


def vp(n: int, p: int):
    if n == 0:
        return None  # infinity
    n = abs(int(n))
    out = 0
    while n % p == 0:
        out += 1
        n //= p
    return out


def phi_power(p: int, h: int) -> int:
    return (p - 1) * p ** (h - 1)


def cost(p: int, e: int, h: int) -> Fraction:
    return Fraction(1, p ** min(vp(e, p), h - 1))


def horizon_cost(p: int, e: int, h0: int, H: int) -> Fraction:
    return sum((cost(p, e, h) for h in range(h0, H + 1)), Fraction())


def first_guaranteed_shell(p: int, e: int, h0: int, B: Fraction) -> int:
    # Exact first strict crossing. Early shell costs are geometric; the tail is flat.
    s = vp(e, p)
    H = h0 - 1
    spent = Fraction()
    while H + 1 <= s + 1:
        H += 1
        spent += cost(p, e, H)
        if spent > B:
            return H
    flat = Fraction(1, p ** s)
    n = int((B - spent) // flat) + 1
    return H + n


def trim(poly, p):
    poly = [int(x) % p for x in poly]
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def eval_mod(poly, a, p):
    out = 0
    for c in reversed(poly):
        out = (out * a + c) % p
    return out


def divide_linear(poly, a, p):
    """Exact synthetic division by X-a. Returns quotient and remainder."""
    if len(poly) == 1:
        return [0], poly[0] % p
    q = [0] * (len(poly) - 1)
    q[-1] = poly[-1] % p
    for j in range(len(poly) - 2, 0, -1):
        q[j - 1] = (poly[j] + a * q[j]) % p
    rem = (poly[0] + a * q[0]) % p
    return trim(q, p), rem


def multiplicity(poly, a, p):
    out = 0
    q = list(poly)
    while len(q) > 1:
        nq, rem = divide_linear(q, a, p)
        if rem:
            break
        out += 1
        q = nq
    return out


def finite_field_case(p: int, e: int, h: int):
    """Enumerate every possible monic initial polynomial through the candidate
    threshold, after removing its irrelevant monomial factor.

    Allowed exponents differ by D=phi(p^h)/gcd(e,phi(p^h)). We do not assume
    the capacity inequality or the packet answer: root multiplicities are
    found by repeated division, then minimum packet degree by set-cover DP.
    Coefficients are in F_p in these finite tests (not all residue extensions).
    """
    eh = phi_power(p, h)
    D = eh // gcd(e, eh)
    s = vp(e, p)
    P = p ** max(h - 1 - s, 0)
    threshold = (p - 1) * P
    max_q_degree = threshold // D
    assert threshold % D == 0
    all_mask = (1 << (p - 1)) - 1
    masks = {0: 0}
    witnesses = {}
    checked = 0
    mult_counter = Counter()
    first_full_degree = None
    max_capacity = Fraction()
    for deg in range(1, max_q_degree + 1):
        for c0 in range(1, p):
            for middle in product(range(p), repeat=deg - 1):
                q = [c0, *middle, 1]
                f = [0] * (deg * D + 1)
                for j, c in enumerate(q):
                    f[j * D] = c
                mask = 0
                roots = []
                for a in range(1, p):
                    m = multiplicity(f, a, p)
                    assert (eval_mod(f, a, p) == 0) == bool(m)
                    if m:
                        mask |= 1 << (a - 1)
                        roots.append(a)
                        mult_counter[m] += 1
                        assert m % P == 0, (p, e, h, q, a, m, P)
                degree = deg * D
                if mask:
                    capacity = Fraction(len(roots) * P, degree)
                    max_capacity = max(max_capacity, capacity)
                    assert capacity <= 1
                    if mask not in masks or degree < masks[mask]:
                        masks[mask] = degree
                        witnesses[mask] = {"q_coefficients_low_to_high": q,
                                           "substitution_exponent": D,
                                           "root_residues": roots}
                if mask == all_mask:
                    first_full_degree = degree if first_full_degree is None else min(first_full_degree, degree)
                checked += 1
    # Exact weighted set-cover DP. A state is the set of residue classes already blocked.
    infinity = 10 ** 30
    dp = [infinity] * (all_mask + 1)
    dp[0] = 0
    prev = {}
    for mask in range(all_mask + 1):
        if dp[mask] == infinity:
            continue
        for new_mask, degree in masks.items():
            united = mask | new_mask
            if united != mask and dp[mask] + degree < dp[united]:
                dp[united] = dp[mask] + degree
                prev[united] = (mask, new_mask)
    packet = []
    at = all_mask
    while at:
        old, used = prev[at]
        packet.append(witnesses[used])
        at = old
    observed_cost = Fraction(dp[all_mask], eh)
    assert dp[all_mask] == threshold
    assert observed_cost == cost(p, e, h)
    return {
        "p": p, "ramification_e": e, "shell_h": h,
        "exponent_step_D": D, "inseparable_multiplicity_P": P,
        "polynomials_exhausted": checked, "distinct_nonempty_root_masks": len(masks) - 1,
        "observed_minimum_packet_degree": dp[all_mask],
        "observed_first_full_cover_degree": first_full_degree,
        "observed_minimum_budget": str(observed_cost),
        "maximum_capacity_ratio": str(max_capacity),
        "nonzero_root_multiplicities_seen": dict(sorted(mult_counter.items())),
        "minimum_cover_example": packet,
    }


def cyclotomic_case(p: int, h: int):
    T = sp.Symbol('T')
    eh = phi_power(p, h)
    f = sp.Poly(sp.cyclotomic_poly(p ** h, T + 1), T, domain=sp.ZZ)
    assert f.degree() == eh
    assert int(f.nth(0)) == p
    assert int(f.LC()) == 1
    reduced = [int(f.nth(j)) % p for j in range(eh + 1)]
    assert reduced == [0] * eh + [1]
    margins = []
    for j in range(1, eh):
        c = int(f.nth(j))
        if c:
            margin = Fraction(vp(c, p)) + Fraction(j, eh) - 1
            assert margin > 0
            margins.append(margin)
    return {
        "p": p, "shell_h": h, "degree": eh,
        "constant_coefficient": p,
        "reduction_mod_p": f"T^{eh}",
        "minimum_strict_interior_Newton_margin": str(min(margins)) if margins else "vacuous",
    }


def resultant_case(p: int, e: int, h: int):
    """For K=Q_p(pi), pi^e=-p, put c=pi^(e/p^k) and d=phi(p^h)/p^k.
    The exact polynomial Q(Y) below has all values (zeta-1)^d-c' as roots,
    for every primitive zeta and every conjugate c' of c. Its coefficient
    Newton inequalities certify v(value)>1/p^k simultaneously.
    """
    T, U, Y = sp.symbols('T U Y')
    k = min(vp(e, p), h - 1)
    pk = p ** k
    eh = phi_power(p, h)
    d = eh // pk
    phi = sp.cyclotomic_poly(p ** h, T + 1)
    r = sp.resultant(phi, T ** d - U - Y, T)
    qexpr = sp.resultant(U ** pk + p, r, U)
    q = sp.Poly(qexpr, Y, domain=sp.ZZ)
    if q.LC() == -1:
        q = -q
    assert q.LC() == 1
    N = eh * pk
    assert q.degree() == N
    base = Fraction(1, pk)
    margins = []
    records = []
    for j in range(N):
        a = int(q.nth(j))
        if not a:
            continue
        val = vp(a, p)
        margin = Fraction(val) - (N - j) * base
        assert margin > 0, (p, e, h, j, a, margin)
        margins.append(margin)
        records.append({"degree": j, "coefficient": str(a), "p_valuation": val,
                        "margin_over_boundary": str(margin)})
    return {
        "p": p, "ramification_e": e, "shell_h": h, "k": k,
        "binomial_exponent_d": d, "witness_valuation": str(base),
        "field_example": f"Q_{p}(pi), pi^{e}=-{p}",
        "norm_polynomial_degree": N,
        "zero_value_multiplicity": min(j for j in range(N + 1) if q.nth(j)),
        "minimum_strict_Newton_margin": str(min(margins)) if margins else "all values zero",
        "norm_polynomial_coefficients_low_to_high": [str(int(q.nth(j))) for j in range(N + 1)],
        "nonzero_coefficient_tests": records,
    }


def comparison_table():
    specs = [
        (2, 1, 1, Fraction(3)),
        (2, 105, 1, Fraction(3)),
        (3, 100, 1, Fraction(3)),
        (5, 1008, 1, Fraction(3)),
        (2, 8, 1, Fraction(3)),
        (2, 24, 1, Fraction(3)),
        (3, 27, 1, Fraction(2)),
        (3, 54, 1, Fraction(2)),
        (5, 100, 1, Fraction(3)),
        (2, 12, 3, Fraction(1)),
        (2, 8, 5, Fraction(3)),
        (3, 100, 1, Fraction(1, 2)),
    ]
    rows = []
    for p, e, h0, B in specs:
        old = h0 + int(e * B)
        new = first_guaranteed_shell(p, e, h0, B)
        before = horizon_cost(p, e, h0, new - 1)
        at = horizon_cost(p, e, h0, new)
        assert before <= B < at
        assert new <= old
        rows.append({"p": p, "ramification_e": e, "wild_valuation_s": vp(e, p),
                     "h0": h0, "budget_B": str(B), "old_guaranteed_H": old,
                     "exact_guaranteed_H": new, "cost_through_H_minus_1": str(before),
                     "cost_through_H": str(at)})
    return rows


def run():
    finite_cases = []
    specs = [
        (2, [1, 2, 3, 4, 6, 8, 12], [1, 2, 3, 4, 5]),
        (3, [1, 2, 3, 4, 6, 9, 12, 18], [1, 2, 3]),
        (5, [1, 2, 4, 5, 10, 20, 25], [1, 2]),
        (7, [1, 2, 7, 14], [1, 2]),
    ]
    for p, es, hs in specs:
        for e in es:
            for h in hs:
                finite_cases.append(finite_field_case(p, e, h))
    cyclotomic = [cyclotomic_case(p, h) for p in [2, 3, 5, 7] for h in [1, 2, 3]]
    # Include tame ramification, pure wild, and mixed tame/wild examples.
    r_specs = [(2, 1, 1), (2, 3, 3), (2, 2, 2), (2, 6, 3), (2, 4, 3),
               (2, 8, 4), (3, 1, 1), (3, 2, 2), (3, 3, 2), (3, 6, 3),
               (5, 4, 1), (5, 5, 2)]
    resultants = [resultant_case(*case) for case in r_specs]
    comparisons = comparison_table()
    return {
        "status": "ALL EXACT CHECKS PASSED",
        "scope": "Finite independent checks, not a substitute for the proof. Initial-polynomial enumeration uses F_p coefficients; resultant examples use pi^e=-p.",
        "python_dependencies": {"sympy": sp.__version__},
        "summary": {
            "finite_field_cases": len(finite_cases),
            "initial_polynomials_exhausted": sum(r["polynomials_exhausted"] for r in finite_cases),
            "cyclotomic_cases": len(cyclotomic),
            "resultant_certificates": len(resultants),
            "comparison_examples": len(comparisons),
        },
        "finite_field_capacity_and_packet_cover": finite_cases,
        "shifted_cyclotomic_certificates": cyclotomic,
        "binomial_obstruction_resultant_certificates": resultants,
        "bound_comparison": comparisons,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('checks.json'))
    args = parser.parse_args()
    data = run()
    args.output.write_text(json.dumps(data, indent=2) + '\n')
    print(data['status'])
    print(json.dumps(data['summary'], indent=2))
    print('Bound comparisons: p e h0 B old_H exact_H')
    for row in data['bound_comparison']:
        print(row['p'], row['ramification_e'], row['h0'], row['budget_B'], row['old_guaranteed_H'], row['exact_guaranteed_H'])
    print('Saved:', args.output)
