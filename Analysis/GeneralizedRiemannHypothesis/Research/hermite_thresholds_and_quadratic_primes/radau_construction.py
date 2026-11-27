#!/usr/bin/env python3
"""Exact certificate for the a=1/2 one-sided Walsh-bias problem.

Run with Python 3.9+ (standard library). The dimension k is the square
of an even integer R. A shell indexed by s consists of cube points with
coordinate sum s. Only the printed decimal summaries use floating point.
"""
from fractions import Fraction as F
from math import comb, isqrt


def nearest_shell(node, root, parity):
    """Round normalized node to nearest allowed shell of the given parity."""
    k = root ** 2
    # If the number of -1 coordinates is parity modulo 2, s = k - 2*parity mod 4.
    residue = (k - 2 * parity) % 4
    grid_point = (node * root - residue) / 4
    return residue + 4 * (grid_point + F(1, 2)).__floor__()


def interpolation_weights(nodes, moments):
    """Integrate the Lagrange cardinal polynomials using prescribed moments."""
    weights = []
    for index, node in enumerate(nodes):
        polynomial = [F(1)]
        denominator = F(1)
        for other_index, other_node in enumerate(nodes):
            if other_index == index:
                continue
            updated = [F(0)] * (len(polynomial) + 1)
            for degree, coefficient in enumerate(polynomial):
                updated[degree] -= other_node * coefficient
                updated[degree + 1] += coefficient
            polynomial = updated
            denominator *= node - other_node
        weights.append(sum(c * m for c, m in zip(polynomial, moments)) / denominator)
    return weights


def shell_distribution(root):
    """Two Gauss-Radau laws supply four nodes, two per endpoint."""
    k = root ** 2
    assert root % 2 == 0
    step = F(1, isqrt(root))
    endpoints = [F(1, 2) - 3 * step, F(1, 2) - step]
    assert endpoints[0] > 0
    ideal = sorted([x for t in endpoints for x in (t, -1 / t)])
    third_moment = sum(t - 1 / t for t in endpoints) / 2
    moments = [F(1), F(0), F(1), third_moment]
    by_shell = {}
    for parity in (0, 1):
        shells = [nearest_shell(node, root, parity) for node in ideal]
        nodes = [F(s, root) for s in shells]
        assert len(set(shells)) == 4
        assert all(-k <= s and 2 * s < root and ((k - s) // 2) % 2 == parity
                   for s in shells)
        weights = interpolation_weights(nodes, moments)
        assert min(weights) > 0
        for degree, target in enumerate(moments):
            assert sum(w * x ** degree for w, x in zip(weights, nodes)) == target
        by_shell.update({s: w / 2 for s, w in zip(shells, weights)})
    return by_shell, third_moment


def slice_biases(k, s, last_level):
    """Expected product of j distinct signs on shell s, for j up to last_level."""
    values = [F(1), F(s, k)]
    for j in range(1, last_level):
        values.append((s * values[j] - j * values[j - 1]) / (k - j))
    return values


def bulk_bound_squared(k, root, shells, first_level):
    """Bound all middle levels using a rational lower bound for shell mass.

    For h=k/2, u=|s|/2, the binomial mass at s divided by its central
    value is at least ((h-u)/(h+u))^u >= exp(-2u^2/(h-u)).
    The central mass is at least 1/sqrt(2k) >= 1/(2R), by Wallis or
    induction. Completeness of the normalized Krawtchouk polynomials
    gives |slice bias_j|^2 <= 1/(mass(s) * binom(k,j)).
    """
    h = k // 2
    u = max(abs(s) for s in shells) // 2
    exponent = F(2 * u ** 2, h - u)
    ceiling = -(-exponent.numerator // exponent.denominator)
    return F(2 * root * 3 ** ceiling, comb(k, first_level))


def certify(root):
    k = root ** 2
    masses, third_moment = shell_distribution(root)
    values = {s: slice_biases(k, s, 5) for s in masses}
    biases = {}
    for j in range(6):
        biases[j] = sum(w * values[s][j] for s, w in masses.items())
        biases[k - j] = sum(w * (-1) ** (((k - s) // 2) % 2) * values[s][j]
                            for s, w in masses.items())
    assert biases[0] == 1
    assert all(biases[j] == 0 for j in (1, 2, k, k - 1, k - 2, k - 3))
    expected = abs(third_moment) * root ** 3 / (k * (k - 1) * (k - 2))
    assert abs(biases[3]) == expected
    assert all(abs(b) < expected for j, b in biases.items() if j not in (0, 3))
    bulk_sq = bulk_bound_squared(k, root, masses, 6)
    assert bulk_sq < expected ** 2
    # F(x)=(x-1/2)(x+2)^2 has uniform mean 3/2 and nonnegative
    # nonconstant Walsh coefficients at x=S/R. Their sum is F(R)-3/2.
    lower = F(3, 2) / ((root - F(1, 2)) * (root + 2) ** 2 - F(3, 2))
    assert 0 < lower < expected
    print(f"k={k:,}, R={root:,}")
    print(f"  occupied coordinate sums: {sorted(masses)}")
    print(f"  least shell probability: {float(min(masses.values())):.8f}")
    print(f"  exact maximum absolute bias: {expected} (degree 3)")
    print(f"  rigorous bracket for k^(3/2) times the optimal bias "
          f"(display rounded): [{float(root ** 3 * lower):.9f}, "
          f"{float(root ** 3 * expected):.9f}]")
    print(f"  middle-level upper bound, same scale (display rounded): "
          f"{float(root ** 6 * bulk_sq) ** 0.5:.9g}")


if __name__ == "__main__":
    for dimension_root in (400, 2500, 10000, 1000000, 100000000):
        certify(dimension_root)
