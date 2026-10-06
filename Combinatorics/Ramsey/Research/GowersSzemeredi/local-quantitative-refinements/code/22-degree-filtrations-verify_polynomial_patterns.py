#!/usr/bin/env python3
"""Exact finite checks of the fixed-center and quadratic propositions.

Pure Python; no floating point and no third-party dependencies. This code
verifies illustrative finite cases, not the general theorems.
"""

from itertools import product
from collections import Counter
import json


def trim(f):
    f = list(f)
    while f and f[-1] == 0:
        f.pop()
    return tuple(f)


def psub(f, g, p):
    return trim([((f[i] if i < len(f) else 0)
                  - (g[i] if i < len(g) else 0)) % p
                 for i in range(max(len(f), len(g)))])


def prem(f, g, p):
    f = list(trim(f))
    g = trim(g)
    inv = pow(g[-1], -1, p)
    while len(f) >= len(g):
        c = f[-1] * inv % p
        pos = len(f) - len(g)
        for j in range(len(g)):
            f[pos+j] = (f[pos+j] - c*g[j]) % p
        while f and not f[-1]:
            f.pop()
    return tuple(f)


def pgcd(f, g, p):
    while g:
        f, g = g, prem(f, g, p)
    inv = pow(f[-1], -1, p)
    return tuple(c*inv % p for c in f)


def pmul(f, g, modulus, p):
    if not f or not g:
        return ()
    ans = [0] * (len(f)+len(g)-1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            ans[i+j] = (ans[i+j]+a*b) % p
    return prem(ans, modulus, p)


def ppow(f, e, modulus, p):
    ans = (1,)
    while e:
        if e & 1:
            ans = pmul(ans, f, modulus, p)
        f = pmul(f, f, modulus, p)
        e >>= 1
    return ans


def irreducible_prime_degree(f, p):
    n = len(f)-1
    assert n in (3, 5)
    x = (0, 1)
    return (ppow(x, p**n, f, p) == x
            and len(pgcd(psub(ppow(x, p, f, p), x, p), f, p)) == 1)


def find_irreducible(n, p):
    for c0 in range(1, p):
        for c1 in range(p):
            f = (c0, c1)+(0,)*(n-2)+(1,)
            if irreducible_prime_degree(f, p):
                return f
    for cs in product(range(p), repeat=n):
        f = cs+(1,)
        if irreducible_prime_degree(f, p):
            return f
    raise AssertionError("No irreducible polynomial found")


def field_norm(x, modulus, p):
    n = len(modulus)-1
    val = ppow(trim(x), (p**n-1)//(p-1), modulus, p)
    assert len(val) <= 1, (p, modulus, x, val)
    return val[0] if val else 0


def norm_checks(p):
    mods = {t: find_irreducible(t, p) for t in (3, 5)}
    hist = {}
    for t in (3, 5):
        hist[t] = Counter(field_norm(v, mods[t], p)
                          for v in product(range(p), repeat=t))
        assert hist[t][0] == 1
        assert all(hist[t][a] == (p**t-1)//(p-1) for a in range(1, p))
    alpha = (pow(2, -1, p), 3*pow(2, -1, p) % p)
    # At center 0, P(alpha*h)-P(-alpha*h) =
    # 2*(alpha**3*N3(h3) + alpha**5*N5(h5)).
    good_norm_pairs = [(a, b) for a, b in product(range(p), repeat=2)
                       if all((pow(t, 3, p)*a + pow(t, 5, p)*b) % p == 0
                              for t in alpha)]
    weighted_count = sum(hist[3][a]*hist[5][b] for a, b in good_norm_pairs)
    assert good_norm_pairs == [(0, 0)]
    assert weighted_count == 1
    # Exhaustive finite-field norm evaluations plus all q^2 norm-value
    # combinations imply this exact count for the full q^8-point space.
    return {
        "prime": p,
        "irreducible_moduli_ascending_coefficients": mods,
        "norm_evaluations": p**3+p**5,
        "norm_value_histograms": hist,
        "reflection_nodes": alpha,
        "norm_pairs_checked": p*p,
        "directions_covered_by_factorized_count": p**8,
        "symmetric_directions_at_origin_including_zero": weighted_count,
    }


def rank_mod(rows, p):
    a = [list(row) for row in rows]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        i = next((i for i in range(r, len(a)) if a[i][j] % p), None)
        if i is None:
            continue
        a[r], a[i] = a[i], a[r]
        c = pow(a[r][j] % p, -1, p)
        a[r] = [x*c % p for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j] % p
                a[i] = [(x-c*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def greedy_degrees(nodes, degrees, p):
    kept = []
    cols = []
    for j in sorted(degrees, reverse=True):
        col = tuple(pow(a, j, p) for a in nodes)
        if rank_mod(cols+[col], p) > len(cols):
            kept.append(j)
            cols.append(col)
    return kept


def budget_checks():
    cases = 0
    for p in (5, 7, 11, 13):
        for k in range(4, p, 2):
            m = k//2
            nodes = [((2*i-1)*pow(2, -1, p)) % p for i in range(1, m+1)]
            for degree in range(1, 4*p+1):
                s = (degree+1)//2
                kept = greedy_degrees(nodes, range(1, 2*s, 2), p)
                t = min(m, s)
                assert kept == list(range(2*s-1, 2*s-2*t, -2))
                assert sum(kept) == t*(2*s-t)
                cases += 1
    p = 5
    nodes = (3, 4)
    assert greedy_degrees(nodes, (1, 5), p) == [5]
    assert greedy_degrees(nodes, (1, 3, 5), p) == [5, 3]
    return {"consecutive_degree_budget_cases": cases,
            "sparse_F5_examples_checked": 2}


def dot(x, y, p):
    return sum(a*b for a, b in zip(x, y)) % p


def matvec(a, x, p):
    return tuple(dot(row, x, p) for row in a)


def quadratic_checks():
    cases = 0
    center_direction_tests = 0
    for p, d in ((3, 2), (5, 2), (3, 3)):
        vectors = list(product(range(p), repeat=d))
        # All diagonal forms plus a dense congruent transform is enough
        # to exercise every rank, radical behavior, and affine offset.
        matrices = []
        diagonals = (product(range(p), repeat=d) if d == 2 else
                     [tuple(1 if i < r else 0 for i in range(d))
                      for r in range(d+1)])
        for diag in diagonals:
            matrices.append(tuple(tuple(diag[i] if i == j else 0
                                        for j in range(d)) for i in range(d)))
        if d == 2:
            for a, b, c in product(range(p), repeat=3):
                matrices.append(((a, b), (b, c)))
        matrices = list(dict.fromkeys(matrices))
        for a in matrices:
            r = rank_mod(a, p)
            radical = [x for x in vectors if not any(matvec(a, x, p))]
            assert len(radical) == p**(d-r)
            for linear in vectors:
                good = any(dot(linear, x, p) for x in radical)
                exceptional = 0
                total = 0
                for z in vectors:
                    az = matvec(a, z, p)
                    grad = tuple((2*u+v) % p for u, v in zip(az, linear))
                    if not any(grad):
                        exceptional += 1
                    count = 0
                    for h in vectors:
                        x_plus = tuple((u+v) % p for u, v in zip(z, h))
                        x_minus = tuple((u-v) % p for u, v in zip(z, h))
                        plus = (dot(x_plus, matvec(a, x_plus, p), p)
                                + dot(linear, x_plus, p)) % p
                        minus = (dot(x_minus, matvec(a, x_minus, p), p)
                                 + dot(linear, x_minus, p)) % p
                        agree = plus == minus
                        assert agree == (dot(grad, h, p) == 0)
                        count += agree
                        center_direction_tests += 1
                    assert count == (p**d if not any(grad) else p**(d-1))
                    total += count-1
                expected_exceptional = 0 if good else p**(d-r)
                assert exceptional == expected_exceptional
                expected = p**d*(p**(d-1)-1)
                expected += expected_exceptional*(p**d-p**(d-1))
                assert total == expected
                cases += 1
    return {"quadratic_maps": cases,
            "exact_center_direction_checks": center_direction_tests}


def additive_extension_checks():
    centers = 0
    fiber_tests = 0
    core_direction_tests = 0
    for p in (5, 7):
        modulus = find_irreducible(3, p)
        vectors = list(product(range(p), repeat=3))
        norms = {v: field_norm(v, modulus, p) for v in vectors}
        half = pow(2, -1, p)
        three_halves = 3*half % p
        core_centers = [(0, 0, 0), (1, 2 % p, 3 % p)]
        added_functions = [
            [t*t % p for t in range(p)],
            [pow(t, 5, p) for t in range(p)],
            [(pow(t, p-1, p)+3*pow(t, 3, p)+2*t+1) % p
             for t in range(p)],
        ]
        for values in added_functions:
            for u in core_centers:
                for b in range(p):
                    actual_total = 0
                    defects = 0
                    for g in range(p):
                        e1 = (values[(b+half*g) % p]
                              - values[(b-half*g) % p]) % p
                        e3 = (values[(b+three_halves*g) % p]
                              - values[(b-three_halves*g) % p]) % p
                        defect = (e3-3*e1) % p
                        defects += bool(defect)
                        actual = 0
                        for h in vectors:
                            # The first reflected equation determines the
                            # scalar core direction uniquely (its coefficient
                            # is 2*(1/2)=1). Check the second directly.
                            up = tuple((x+half*y) % p for x, y in zip(u, h))
                            um = tuple((x-half*y) % p for x, y in zip(u, h))
                            scalar_h = (-e1-norms[up]+norms[um]) % p
                            up3 = tuple((x+three_halves*y) % p
                                        for x, y in zip(u, h))
                            um3 = tuple((x-three_halves*y) % p
                                        for x, y in zip(u, h))
                            second = (3*scalar_h+norms[up3]-norms[um3]+e3) % p
                            actual += second == 0
                            core_direction_tests += 1
                        assert actual == (p*p+p+1 if defect else 1)
                        assert actual > 0
                        actual_total += actual
                        fiber_tests += 1
                    assert actual_total == p+(p*p+p)*defects
                    centers += 1
    return {
        "centers_checked": centers,
        "extra_direction_fibers_checked": fiber_tests,
        "core_directions_examined": core_direction_tests,
        "extra_block_dimension": 1,
        "output": "all fibers nonempty; exact third-difference formula holds",
    }


def main():
    result = {
        "fixed_center_norms": [norm_checks(p) for p in (5, 7)],
        "rank_budgets": budget_checks(),
        "quadratics": quadratic_checks(),
        "additive_extensions": additive_extension_checks(),
        "arithmetic": "exact integer arithmetic modulo the indicated prime",
        "status": "PASS",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
