#!/usr/bin/env python3
"""Exact finite checks of the support/Wigner identities.

These computations test the transcription and normalization. They are not
the universal proof and are not a Lean or iPRA proof certificate.
The algebra is Laurent polynomials with Gaussian-rational coefficients.
"""
from fractions import Fraction as F
import json
import random

ZERO = (F(0), F(0))


def add(z, w):
    return (z[0] + w[0], z[1] + w[1])


def mul(z, w):
    return (z[0] * w[0] - z[1] * w[1],
            z[0] * w[1] + z[1] * w[0])


def scale(z, t):
    return (z[0] * t, z[1] * t)


def padd(p, q):
    return {k: add(p.get(k, ZERO), q.get(k, ZERO)) for k in p.keys() | q.keys()}


def pmul(p, q):
    result = {}
    for k, z in p.items():
        for j, w in q.items():
            result[k + j] = add(result.get(k + j, ZERO), mul(z, w))
    return result


def derivative(p):
    return {k: mul((F(0), F(k)), z) for k, z in p.items()}


def conjugate(p):
    return {-k: (z[0], -z[1]) for k, z in p.items()}


def support(a0, coefficients):
    p = {0: (a0, F(0))}
    for n, (a, b) in enumerate(coefficients, 1):
        p[n] = (a / 2, -b / 2)
        p[-n] = (a / 2, b / 2)
    return p


def check(a0, coefficients):
    p = support(a0, coefficients)
    # Complex coordinate gamma=(p+i*p')*exp(i theta).
    iprime = {n: mul((F(0), F(1)), z) for n, z in derivative(p).items()}
    gamma = {n + 1: z for n, z in padd(p, iprime).items()}
    signed_mean = pmul(conjugate(gamma), derivative(gamma)).get(0, ZERO)
    area_over_pi = signed_mean[1]
    assert signed_mean[0] == 0
    # Opposite-point midpoint selects even frequencies of gamma.
    midpoint = {n: z for n, z in gamma.items() if n % 2 == 0}
    wigner_mean = pmul(conjugate(midpoint), derivative(midpoint)).get(0, ZERO)
    one_pass_wigner_over_pi = wigner_mean[1] / 2
    energy = sum((n * n - 1) * (a * a + b * b)
                 for n, (a, b) in enumerate(coefficients, 1))
    odd = sum((n * n - 1) * (a * a + b * b)
              for n, (a, b) in enumerate(coefficients, 1) if n % 2)
    even = energy - odd
    assert energy >= 0 and odd >= 0 and even >= 0
    assert area_over_pi == a0 * a0 - energy / 2
    assert one_pass_wigner_over_pi == -odd / 4
    deficit_over_2pi2 = (2 * a0 * a0 - 2 * area_over_pi
                         - 4 * abs(one_pass_wigner_over_pi))
    assert deficit_over_2pi2 == even
    return {
        "degree": len(coefficients),
        "area_over_pi": str(area_over_pi),
        "one_pass_wigner_area_over_pi": str(one_pass_wigner_over_pi),
        "improved_deficit_over_2pi_squared": str(even),
        "constant_width": even == 0,
    }


def main():
    named = {
        "circle": check(F(2), [(F(3), F(-4))]),
        "constant_width_non_circle": check(F(1), [(F(0), F(0)),
            (F(0), F(0)), (F(1, 16), F(0))]),
        "even_mode_oval": check(F(1), [(F(0), F(0)), (F(1, 8), F(0))]),
        "mixed_modes": check(F(2), [(F(5), F(-2)), (F(1, 16), F(1, 20)),
            (F(1, 32), F(-1, 40)), (F(1, 128), F(0))]),
    }
    rng = random.Random(151206684)
    for _ in range(100):
        coefficients = [(F(rng.randrange(-4, 5), rng.randrange(1, 12)),
                         F(rng.randrange(-4, 5), rng.randrange(1, 12)))
                        for _ in range(rng.randrange(1, 10))]
        # A rational certificate that p+p'' >= 1 for every angle.
        a0 = 1 + sum((n * n - 1) * (abs(a) + abs(b))
                     for n, (a, b) in enumerate(coefficients, 1))
        check(F(a0), coefficients)
    for M in range(1, 101):
        assert sum(F(1, (2*j)**2 - 1) for j in range(1, M + 1)) == F(1, 2) * (1 - F(1, 2*M + 1))
        assert sum(F(1, j*j - 1) for j in range(2, M + 2)) <= F(3, 4)
    print(json.dumps({"status": "passed", "exact_laurent_cases": 104,
                      "telescoping_checks": 200, "named_examples": named}, indent=2))


if __name__ == "__main__":
    main()
