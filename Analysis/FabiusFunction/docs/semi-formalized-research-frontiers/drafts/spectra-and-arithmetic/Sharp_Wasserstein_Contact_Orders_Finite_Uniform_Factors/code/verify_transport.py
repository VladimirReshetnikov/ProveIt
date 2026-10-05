#!/usr/bin/env python3
"""Exact finite CDF checks of the clipping identity and Fourier coefficients.

Run from the package root: python code/verify_transport.py
All calculations are rational/integer. These checks are independent finite
corroboration, not proofs for general measures or infinite Fourier products.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import json
import math
import random


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def law(points, weights):
    out = {}
    total = sum(weights)
    for x, w in zip(points, weights):
        out[F(x)] = out.get(F(x), F(0)) + F(w, total)
    return out


def convolution(p, q):
    out = {}
    for x, a in p.items():
        for y, b in q.items():
            out[x + y] = out.get(x + y, F(0)) + a * b
    return out


def w1_cdf(p, q):
    nodes = sorted(set(p) | set(q))
    signed_cdf = F(0)
    result = F(0)
    for j, x in enumerate(nodes[:-1]):
        signed_cdf += p.get(x, F(0)) - q.get(x, F(0))
        result += abs(signed_cdf) * (nodes[j + 1] - x)
    return result


def clipped(p, lo, hi):
    out = {}
    displacement = F(0)
    for z, w in p.items():
        zz = max(lo, min(z, hi))
        out[zz] = out.get(zz, F(0)) + w
        displacement += abs(z - zz) * w
    return out, displacement


def polynomial_multiply(p, q):
    """Bivariate polynomials with keys (delta_degree, h_degree)."""
    out = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            key = (a + c, b + d)
            out[key] = out.get(key, F(0)) + x * y
    return out


def run():
    rng = random.Random(20261005)
    clipping_count = 0
    strictly_improved = 0
    for case in range(1200):
        a = rng.randint(-5, 0)
        b = a + rng.randint(0, 7)
        c = rng.randint(-4, 1)
        d = c + rng.randint(0, 6)
        mu = law([rng.randint(a, b) for _ in range(5)],
                 [rng.randint(1, 9) for _ in range(5)])
        sigma = law([rng.randint(c, d) for _ in range(4)],
                    [rng.randint(1, 9) for _ in range(4)])
        nu = law([rng.randint(-20, 20) for _ in range(7)],
                 [rng.randint(1, 9) for _ in range(7)])
        nu_k, saved = clipped(nu, F(a-d), F(b-c))
        original = w1_cdf(mu, convolution(sigma, nu))
        localized = w1_cdf(mu, convolution(sigma, nu_k))
        require(original == localized + saved, f'clipping case {case}')
        eta = convolution(sigma, nu)
        eta_k = convolution(sigma, nu_k)
        tv = lambda p,q: sum(abs(p.get(x,F(0))-q.get(x,F(0))) for x in set(p)|set(q))/2
        require(tv(mu, eta_k) <= tv(mu, eta), f'TV clipping case {case}')
        clipping_count += 1
        strictly_improved += saved > 0

    coefficients = 0
    for B in range(2, 6):
        for n in range(1, 10):
            T = B ** n
            p = {(0, 1): F(1, T)}
            for k in range(1, n+1):
                p = polynomial_multiply(p, {(1, 0): F(k*B), (0, 1): F(1, T)})
            for r in range(1, n+1):
                e = n+1-r
                symmetric = sum(math.prod(c) for c in combinations(range(1, n+1), e))
                expected = F(B**e * symmetric, T**r)
                require(p[(e, r)] == expected, f'coefficient B={B}, n={n}, r={r}')
                require(expected > 0, 'coefficient positivity')
                require(all(a+b == n+1 for a, b in p), 'homogeneity')
                coefficients += 1
    triple = F(math.factorial(2) * 2**2 * 11, 8**2)
    require(triple == F(11, 8), 'worked example coefficient')
    return {
        'status': 'passed',
        'arithmetic': 'exact integer and Fraction',
        'random_seed': 20261005,
        'clipping_identity_cases': clipping_count,
        'total_variation_clipping_cases': clipping_count,
        'strictly_improved_clipping_cases': strictly_improved,
        'fourier_joint_polynomial_coefficients': coefficients,
        'worked_example_coefficient_over_P2': str(triple),
        'limitations': [
            'Finite atomic laws only in the CDF checks.',
            'Polynomial checks verify constants in the finite leading Taylor term.',
            'General clipping, analytic remainders, and the infinite product require the proofs.'
        ]
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
        default=Path(__file__).resolve().parents[1] / 'data' / 'transport_verification.json')
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
