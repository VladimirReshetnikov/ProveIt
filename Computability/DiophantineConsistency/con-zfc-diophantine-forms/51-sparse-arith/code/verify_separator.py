#!/usr/bin/env python3
"""Independent exact finite checks for the new arithmetic root separator.

The unbounded theorem is proved in ../FINALIZER_PROOF.md. These
checks establish the formal norm identity and inspect finite guard/control
families using exact signed squareclasses, without floating point or an
external algebra package. No assertion statements are used.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import gcd, isqrt
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def square(n):
    return n >= 0 and isqrt(n) ** 2 == n


@lru_cache(None)
def radical(n):
    """Return signed squarefree d and a>=0 with sqrt(n)=a*sqrt(d)."""
    if n == 0:
        return 1, 0
    d = -1 if n < 0 else 1
    a = 1
    n = abs(n)
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        a *= p ** (exponent // 2)
        if exponent % 2:
            d *= p
        p += 1
    d *= n
    return d, a


def rational_signed_sum(radicals, weights):
    """Whether some independently signed weighted root sum is rational."""
    pieces = [radical(n) for n in radicals]
    for signs in product((-1, 1), repeat=len(pieces)):
        coefficients = defaultdict(int)
        for sign, weight, (d, a) in zip(signs, weights, pieces):
            coefficients[d] += sign * weight * a
        if all(d == 1 or a == 0 for d, a in coefficients.items()):
            return True
    return False


def add(a, b, sign=1):
    c = dict(a)
    for e, value in b.items():
        c[e] = c.get(e, 0) + sign * value
        if not c[e]:
            del c[e]
    return c


def mul(a, b):
    c = defaultdict(int)
    for e, x in a.items():
        for f, y in b.items():
            c[tuple(v + w for v, w in zip(e, f))] += x * y
    return {e: value for e, value in c.items() if value}


def scale(a, c):
    return {e: c * v for e, v in a.items() if c * v}


def norm_identity():
    one = {(0, 0, 0, 0): 1}
    variables = []
    for i in range(4):
        e = [0] * 4
        e[i] = 1
        variables.append({tuple(e): 1})
    t, u, v, w = variables
    product_form = one
    for signs in product((-1, 1), repeat=3):
        factor = t
        for sign, root in zip(signs, (u, v, w)):
            factor = add(factor, scale(root, sign))
        product_form = mul(product_form, factor)
    t2, a0, a1, a2 = [mul(x, x) for x in (t, u, v, w)]
    vv = add(add(add(t2, a2), a0, -1), a1, -1)
    vv2 = mul(vv, vv)
    ww = add(add(vv2, scale(mul(t2, a2), 4)), scale(mul(a0, a1), 4), -1)
    formula = add(mul(ww, ww), scale(mul(mul(t2, a2), vv2), 16), -1)
    require(formula == product_form, "Eight-factor norm identity failed")
    require(formula.get((8, 0, 0, 0)) == 1, "Norm not monic in t")
    return {"polynomial_terms": len(formula), "identity": "PASS", "monic_degree": 8}


def main():
    result = {"norm": norm_identity()}
    count = 0
    for b in range(-7, 8):
        if abs(b) <= 1:
            continue
        for j in range(-9, 10):
            if gcd(b, j) != 1 or square(b * j):
                continue
            for a, r in product(range(-6, 11), repeat=2):
                for k in (-3, -1, 1, 2):
                    require(not rational_signed_sum((b * j, a, r), (1, b, b * k)),
                            f"Coprime first-root lemma failed: {b,j,a,r,k}")
                    count += 1
    result["coprime_first_root_cases"] = count

    count = 0
    for r0 in range(-21, 22, 2):
        if square(r0):
            continue
        for r1, r2 in product(range(-16, 17, 4), repeat=2):
            for k in range(-3, 4):
                for b in (-1, 1):
                    require(not rational_signed_sum((r0, r1, r2), (1, b, b * k)),
                            f"Odd first-root parity lemma failed: {r0,r1,r2,k,b}")
                    count += 1
    result["unit_parity_cases"] = count

    count = 0
    for p in range(-12, 13):
        for k in range(-5, 6):
            if not k:
                continue
            a = (p * p - 4) * k * k + 4
            for r in range(-40, 81, 4):
                actual = rational_signed_sum((a, r), (1, k))
                require(actual == (square(a) and square(r)),
                        f"Pell-remainder lemma failed: {p,k,r,a}")
                count += 1
    result["pell_remainder_cases_including_odd_P"] = count

    # Exact counterexamples to dropping guards, checked rather than just listed.
    require(rational_signed_sum((32, 8, 0), (1, 2, 2)),
            "Expected failed-coprimality control did not trigger")
    require(not square(32), "First guard control unexpectedly square")
    require(rational_signed_sum((-1, -1, 0), (1, 1, 1)),
            "Expected failed-mod-four control did not trigger")
    require(rational_signed_sum((4, -4), (1, 0)),
            "Expected K=0 control did not trigger")
    require(not square(-4), "K=0 control unexpectedly square")
    require(rational_signed_sum((-12, -3), (1, 2)),
            "Expected R nonmultiple-four control did not trigger")
    result["negative_controls"] = {
        "coprimality_needed": {"b": 2, "J": 16, "radicands": [32, 8, 0]},
        "unit_mod_four_needed": {"radicands": [-1, -1, 0]},
        "K_nonzero_needed": {"P": 0, "K": 0, "R": -4, "A": 4},
        "R_mod_four_needed": {"P": 0, "K": 2, "R": -3, "A": -12},
    }
    result["status"] = "PASS"
    result["scope"] = "Exact norm identity and finite lemma/control checks; not a substitute for the unbounded mathematical proof."
    output = Path(__file__).resolve().parents[1]/"certificates/separator.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
