#!/usr/bin/env python3
"""Independent finite and numerical checks for higher spectral face identities.

All rational checks use fractions.Fraction. Numerical comparisons are diagnostics,
not interval certificates. The quadrature is ordinary Gauss--Legendre quadrature
on each ordering sector of a triangle; it is independent of the harmonic formula.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial
from pathlib import Path
import json
import mpmath as mp


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for h in range(total + 1):
            for tail in compositions(total - h, length - 1):
                yield (h,) + tail


@lru_cache(None)
def complete_harmonic(n, degree):
    """h_degree(1,1/2,...,1/n), including h_0=1."""
    h = [Q(1)] + [Q(0)] * degree
    for j in range(1, n + 1):
        for q in range(1, degree + 1):
            h[q] += h[q - 1] / j
    return h[degree]


def monomial_face_harmonic(masses, degree):
    k = len(masses)
    total = Q(0)
    for h in compositions(degree, k):
        active = [j for j, value in enumerate(h) if value]
        d = len(active)
        term = degree * (-1) ** (k - d) * factorial(k - d)
        term *= complete_harmonic(degree - 1, k - d)
        for j in active:
            term *= masses[j] ** h[j] / h[j]
        total += term
    return total


def poly_mul(a, b, maxdegree):
    c = [Q(0)] * (maxdegree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= maxdegree:
                c[i + j] += x * y
    return c


def rising_poly(h, maxdegree):
    result = [Q(1)]
    for j in range(h):
        result = poly_mul(result, [Q(j), Q(1)], maxdegree)
    return result


def monomial_face_dirichlet(masses, degree):
    """Zero coefficient via a distinct rational Dirichlet-moment construction.

    Q_k(s) int H prod(t_i^(s-1)) = m!/s^k * sum_T (-1)^(k-|T|)
      [u^m] prod_(i in T)(1-B_i u)^(-s)/(1+|T|s)_(m-1).
    """
    k = len(masses)
    coefficient = Q(0)
    for size in range(1, k + 1):
        for subset in combinations(range(k), size):
            numerator = [Q(0)] * (k + 1)
            for h in compositions(degree, size):
                term = [Q(1)]
                scale = Q(1)
                for j, value in zip(subset, h):
                    term = poly_mul(term, rising_poly(value, k), k)
                    scale *= masses[j] ** value / factorial(value)
                for d in range(k + 1):
                    numerator[d] += scale * term[d]
            inverse = [Q(1)]
            for j in range(1, degree):
                inverse = poly_mul(
                    inverse,
                    [Q(1, j) * (-Q(size, j)) ** d for d in range(k + 1)],
                    k,
                )
            product = poly_mul(numerator, inverse, k)
            coefficient += (-1) ** (k - size) * factorial(degree) * product[k]
    return coefficient


def face_value(masses, proportions, f):
    k = len(masses)
    ans = mp.mpf(0)
    for size in range(1, k + 1):
        for subset in combinations(range(k), size):
            weight = sum(proportions[j] for j in subset)
            center = sum(proportions[j] * masses[j] for j in subset) / weight
            ans += (-1) ** (k - size) * weight * f(center)
    return ans


def gauss_triangle_face(masses, f, order=22):
    nodes, weights = mp.gauss_quadrature(order, "legendre")
    nodes = [(x + 1) / 2 for x in nodes]
    weights = [w / 2 for w in weights]
    ans = mp.mpf(0)
    for permutation in permutations(range(3)):
        for u, wu in zip(nodes, weights):
            for v, wv in zip(nodes, weights):
                raw = [1, u, u * v]
                den = sum(raw)
                proportions = [mp.mpf(0)] * 3
                for j, position in enumerate(permutation):
                    proportions[position] = raw[j] / den
                ans += wu * wv * face_value(masses, proportions, f) / (u * v)
    return ans


def resolvent_at_one(m, B):
    """sum_(n>=1) (n^2+B)^(-m), from an ordinary binomial/zeta series."""
    term_scale = mp.mpf(1)
    ans = mp.zeta(2 * m)
    for j in range(1, 220):
        term_scale *= -(m + j - 1) * B / j
        term = term_scale * mp.zeta(2 * m + 2 * j)
        ans += term
        if abs(term) < mp.mpf("1e-44"):
            break
    return ans


def depth_two_lattice(k, delta):
    """sum_n Li_(1,k-1)(delta/(n^2+delta)), positive outer-order series."""
    harmonic = mp.mpf(0)
    ans = mp.mpf(0)
    for m in range(1, 100):
        if m >= 2:
            harmonic += mp.mpf(1) / (m - 1) ** (k - 1)
            term = harmonic * delta ** m / m * resolvent_at_one(m, delta)
            ans += term
            if abs(term) < mp.mpf("1e-39"):
                break
    return ans


def gamma_zero_mass(B):
    if B == 0:
        return -mp.log(2 * mp.pi)
    u = mp.pi * mp.sqrt(B)
    return mp.log(u / mp.sinh(u)) - mp.log(2 * mp.pi)


def repeated_face_one_integral(k, delta):
    coefficients = [
        (-1) ** m * mp.zeta(2 * m) * (m - 1) / m
        for m in range(2, 110)
    ]

    def integrand(t):
        if t == 1:
            return 0
        u = delta * t
        value = mp.polyval(list(reversed(coefficients)), u)
        return delta ** 2 * value * (-mp.log1p(-t)) ** (k - 1)

    return (-1) ** (k - 1) * mp.quad(integrand, [0, mp.mpf("0.5"), 1])


def main():
    exact = []
    for k in range(2, 6):
        masses = tuple(Q(j * j + 1, j + 2) for j in range(k))
        for m in range(2, 9):
            a = monomial_face_harmonic(masses, m)
            b = monomial_face_dirichlet(masses, m)
            assert a == b
            exact.append({"k": k, "m": m, "value": str(a), "pass": True})
    for k in range(2, 8):
        masses = tuple(Q(j, 3) for j in range(k))
        predicted = (-1) ** (k - 1) * factorial(k - 2) * sum(
            (masses[i] - masses[j]) ** 2 for i in range(k) for j in range(i)
        )
        assert monomial_face_harmonic(masses, 2) == predicted
    examples = {
        str(m): str(monomial_face_harmonic((Q(0), Q(1), Q(2)), m))
        for m in range(2, 9)
    }
    mp.mp.dps = 48
    numerical = []
    masses = [mp.mpf("0.2"), mp.mpf("0.7"), mp.mpf("1.3")]
    for m in [3, 4, 6]:
        exactvalue = monomial_face_harmonic((Q(1, 5), Q(7, 10), Q(13, 10)), m)
        predicted = mp.mpf(exactvalue.numerator) / exactvalue.denominator
        observed = gauss_triangle_face(masses, lambda x, m=m: x ** m, 24)
        error = abs(observed - predicted)
        numerical.append({"check": "direct_triangle_monomial", "degree": m,
                          "lhs": mp.nstr(observed, 42), "rhs": mp.nstr(predicted, 42),
                          "absolute_residual": mp.nstr(error, 8)})
        assert error < mp.mpf("1e-20")
    delta = mp.mpf("0.3")
    for k in range(2, 7):
        observed = repeated_face_one_integral(k, delta)
        predicted = (-1) ** (k - 1) * factorial(k - 1) * depth_two_lattice(k, delta)
        error = abs(observed - predicted)
        numerical.append({"check": "one_integral_vs_depth_two_polylog_lattice", "k": k,
                          "lhs": mp.nstr(observed, 42), "rhs": mp.nstr(predicted, 42),
                          "absolute_residual": mp.nstr(error, 8)})
        assert error < mp.mpf("1e-35")
    predicted = 2 * depth_two_lattice(3, delta)
    for order in [16, 24, 32]:
        observed = gauss_triangle_face([0, 0, delta], gamma_zero_mass, order)
        error = abs(observed - predicted)
        numerical.append({"check": "direct_gamma_triangle_vs_polylog_lattice", "order": order,
                          "lhs": mp.nstr(observed, 42), "rhs": mp.nstr(predicted, 42),
                          "absolute_residual": mp.nstr(error, 8)})
    assert error < mp.mpf("1e-25")
    report = {
        "exact_harmonic_vs_dirichlet_checks": exact,
        "quadratic_variance_checks": 6,
        "three_mass_0_1_2_monomials": examples,
        "numerical_working_dps": mp.mp.dps,
        "numerical_checks": numerical,
        "qualification": "Finite algebra and high-precision numerical diagnostics; no interval certificate.",
    }
    target = Path(__file__).resolve().parents[1]/"results"/"spectral_verification.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"exact_checks": len(exact) + 6,
                      "numerical_checks": len(numerical),
                      "max_numerical_residual": max(mp.mpf(x["absolute_residual"]) for x in numerical),
                      "output": str(target)}, default=str))


if __name__ == "__main__":
    main()
