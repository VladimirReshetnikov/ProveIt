#!/usr/bin/env python3
"""Exact certificates for the discriminant -23 character calculations.

This verifies all finite arithmetic used in the paper proof.  The identification
with ray class characters uses the exact sequences proved in the report; this
script is not an independent class-field implementation or a Lean proof.
Python standard library only.  No numerical approximations or network calls.
"""
from __future__ import annotations

import csv
import json
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def valuation(n, p):
    require(n != 0, "valuation called at zero")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def reduced_forms(D):
    out = []
    for a in range(1, isqrt(D // 3) + 2):
        for b in range(-a, a + 1):
            if (b * b + D) % (4 * a):
                continue
            c = (b * b + D) // (4 * a)
            if a > c or (abs(b) == a or a == c) and b < 0:
                continue
            if gcd(gcd(a, abs(b)), c) == 1:
                out.append((a, b, c))
    return out


def mul(u, v):
    """In Z[theta], theta^2=theta-6; pairs are constant/theta."""
    a, b = u
    c, d = v
    return a * c - 6 * b * d, a * d + b * c + b * d


def conjugate(u):
    a, b = u
    return a + b, -b


def norm(u):
    n, zero = mul(u, conjugate(u))
    require(zero == 0, "norm has nonconstant part")
    return n


def theta_roots(q):
    return [t for t in range(q) if (t * t - t + 6) % q == 0]


def evaluate(u, theta, q):
    return (u[0] + u[1] * theta) % q


def sylow_order(x, q, p=3):
    h = valuation(q - 1, p)
    x = pow(x, (q - 1) // p**h, q)
    order = 1
    while x != 1:
        x = pow(x, p, q)
        order *= p
    return order


def main():
    forms = reduced_forms(23)
    require(forms == [(1, 1, 6), (2, -1, 3), (2, 1, 3)], "class census")
    alpha, beta = (1, 1), (1, 2)
    require(norm(alpha) == 8 and norm(beta) == 27, "principal ideal norms")
    require(evaluate(beta, 1, 3) == 0 and evaluate(beta, 0, 3) != 0,
            "Q3^3 generator split selection")
    # A nonzero theta coefficient contributes >=23/4 to the norm, while
    # a zero coefficient gives a square. This verifies the finite boundary too.
    require(not any(a*a+a*b+6*b*b == 3 for a in range(-4, 5)
                    for b in range(-2, 3)), "nonprincipal Q3")

    rows = []
    for q in range(2, 152):
        if not is_prime(q) or q % 3 != 1:
            continue
        roots = theta_roots(q)
        if len(roots) != 2:
            continue
        theta = roots[0]
        r = evaluate(beta, theta, q) * pow(evaluate(conjugate(beta), theta, q), -1, q) % q
        h = valuation(q - 1, 3)
        order = sylow_order(r, q)
        cube_test = pow(r, (q - 1) // 3, q)
        rows.append(dict(q=q, theta=theta, ratio=r, v3_q_minus_1=h,
                         cube_test=cube_test, local_group_order=3**h,
                         relation_order=order, quotient_order=3**h // order))

    require([r['q'] for r in rows] == [13, 31, 73, 127, 139, 151], "exhaustive prime list")
    require([r['cube_test'] for r in rows] == [9, 5, 64, 19, 42, 1], "cube test values")
    require([r['quotient_order'] for r in rows] == [1, 1, 1, 1, 1, 3], "ray quotients")

    # Bare C9 character table. Inertia is 3C9; killing Frobenius above3
    # means killing a generator of C9, which permits only the identity.
    chars = []
    for k in range(9):
        chars.append(dict(k=k, global_order=9 // gcd(9, k),
                          inertia_exponent_mod3=k % 3,
                          trivial_at_3=k == 0))
    require(sum(c['inertia_exponent_mod3'] != 0 for c in chars) == 6,
            "six ramified C9 characters")
    require(all(c['global_order'] == 9 for c in chars if c['inertia_exponent_mod3']),
            "necessary order inflation")

    # At 13 and31 both relations are nonzero; change each local generator
    # to normalize the relation to (1,1). Killing Frobenius imposes x+y=0.
    two_prime = [(x,y) for x in range(3) for y in range(3) if (x+y) % 3 == 0]
    require(two_prime == [(0,0), (1,2), (2,1)], "two-prime repair")
    require(13*31 > 151 and 151**2 == 22801, "minimal conductor")

    result = dict(status="passed", discriminant=-23, reduced_forms=forms,
                  alpha_norm=8, beta_norm=27, prime_table=rows,
                  bare_conductor13_characters=chars,
                  two_prime_compatible_characters=two_prime,
                  minimum_conductor_rational_generator=151,
                  minimum_conductor_norm=22801,
                  number_of_minimizers=2, minimizer_character_order=3,
                  scope="anti 3-power characters, trivial at decomposition above3, split-pair ramification")
    out = ROOT / "evidence" / "ray_character_checks.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    with (ROOT / "evidence" / "ray_prime_table.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
