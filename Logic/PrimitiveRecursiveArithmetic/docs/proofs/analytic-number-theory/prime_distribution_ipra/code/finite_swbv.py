#!/usr/bin/env python3
"""Exact finite examples for the SW/BV report's algebraic lemmas.

These tests verify finite instances and algebraic bookkeeping. They are not
proofs of the general lemmas, of Siegel--Walfisz, or of Bombieri--Vinogradov.
Only Python's standard library is needed.
"""

from fractions import Fraction as F
from itertools import product
import json


def factors(n):
    """Bounded trial division; returns the prime/exponent table of n >= 1."""
    assert n >= 1
    result = []
    remaining = n
    for p in range(2, n + 1):
        exponent = 0
        # A bounded loop is intentional, to expose the primitive recursive form.
        for _ in range(n):
            if remaining % p == 0:
                remaining //= p
                exponent += 1
            else:
                break
        if exponent:
            result.append((p, exponent))
        if remaining == 1:
            break
    return result


def mobius(n):
    fs = factors(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


def convolution(f, g, n):
    return sum((f[d] * g[n // d] for d in range(1, n + 1) if n % d == 0), F(0))


def convolve(f, g):
    assert len(f) == len(g)
    return [F(0)] + [convolution(f, g, n) for n in range(1, len(f))]


def truncate(f, cutoff, lower=True):
    return [v if ((n <= cutoff) == lower) else F(0) for n, v in enumerate(f)]


def vaughan_checks(bound=120):
    # Signed and nonintegral weights test the full stated generalization.
    weight = lambda p: F((p % 7) - 3, p + 1)
    one = [F(0)] + [F(1)] * bound
    mu = [F(0)] + [F(mobius(n)) for n in range(1, bound + 1)]
    logw = [F(0)] + [sum((e * weight(p) for p, e in factors(n)), F(0))
                     for n in range(1, bound + 1)]
    lam = [F(0)]
    for n in range(1, bound + 1):
        fs = factors(n)
        lam.append(weight(fs[0][0]) if len(fs) == 1 else F(0))
    epsilon = [F(0)] * (bound + 1)
    epsilon[1] = F(1)
    assert convolve(mu, one) == epsilon
    assert convolve(one, lam) == logw
    assert convolve(mu, logw) == lam
    checks = 0
    for u, v in product(range(1, 7), repeat=2):
        mu_low = truncate(mu, u)
        mu_high = truncate(mu, u, False)
        lam_low = truncate(lam, v)
        lam_high = truncate(lam, v, False)
        term1 = convolve(mu_low, logw)
        term2 = convolve(convolve(mu_low, one), lam_low)
        term3 = convolve(convolve(mu_high, one), lam_high)
        for n in range(1, bound + 1):
            assert lam[n] == lam_low[n] + term1[n] - term2[n] + term3[n]
            checks += 1
    return checks


# Gaussian rationals are pairs (real part, imaginary part).
def add(z, w):
    return (z[0] + w[0], z[1] + w[1])


def neg(z):
    return (-z[0], -z[1])


def sub(z, w):
    return add(z, neg(w))


def mul(z, w):
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def conjugate(z):
    return (z[0], -z[1])


def norm2(z):
    return z[0] ** 2 + z[1] ** 2


def sumc(values):
    result = (F(0), F(0))
    for z in values:
        result = add(result, z)
    return result


def inner(u, v):
    return sumc(mul(conjugate(z), w) for z, w in zip(u, v))


def gram_checks():
    entries = [(F(0), F(0)), (F(1), F(0)), (F(-1, 2), F(0)), (F(0), F(1, 3))]
    checks = 0
    for flat in product(entries, repeat=4):
        matrix = [flat[:2], flat[2:]]
        gram = [[sumc(mul(matrix[r][n], conjugate(matrix[s][n])) for n in range(2))
                 for s in range(2)] for r in range(2)]
        # Rational symmetric majorants, supplied as the theorem's certificates.
        majorant = [[abs(z[0]) + abs(z[1]) for z in row] for row in gram]
        assert majorant[0][1] == majorant[1][0]
        assert all(norm2(gram[r][s]) <= majorant[r][s] ** 2
                   for r, s in product(range(2), repeat=2))
        limit = max(sum(row) for row in majorant)
        for vector in product(entries, repeat=2):
            out = [sumc(mul(matrix[r][n], vector[n]) for n in range(2))
                   for r in range(2)]
            assert sum(map(norm2, out)) <= limit * sum(map(norm2, vector))
            checks += 1
    # Verify the complex Lagrange sum-of-squares identity separately.
    lagrange = 0
    for u0, u1, v0, v1 in product(entries, repeat=4):
        lhs = (norm2(u0) + norm2(u1)) * (norm2(v0) + norm2(v1))
        lhs -= norm2(inner([u0, u1], [v0, v1]))
        rhs = norm2(sub(mul(u0, v1), mul(u1, v0)))
        assert lhs == rhs
        lagrange += 1
    return checks, lagrange


def inclusion_checks():
    count = 0
    for k in range(0, 35):
        threshold = 16 * (k + 1) ** 2
        for t in range(threshold, threshold + 50):
            assert t ** k <= 2 ** (t // 2)
            count += 1
    return count


def main():
    gram, lagrange = gram_checks()
    report = {
        "status": "all exact finite checks passed",
        "scope": "finite instances; not a proof of the general or analytic theorems",
        "weighted_vaughan_instances": vaughan_checks(),
        "gaussian_rational_gram_instances": gram,
        "complex_lagrange_identities": lagrange,
        "integer_range_inclusions": inclusion_checks(),
        "arithmetic": "fractions.Fraction and unbounded Python integers; no floating point",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
