"""Recover quantiles from transport-law observations using exact rational arithmetic.

The example density is 1/2 + x on [0,1]. Its level-ell finite law moves each
dyadic cell to the LEFT endpoint. Coupling each point to that endpoint has
cost at most 2**(-ell). The compressed oracle computes expectations under
this very finite law, including the mass at 0, by two prefix moment formulas.
The exact target CDF is used only in regression checks.

Run: python3 examples/quantiles.py  (Python 3.9+, no third-party packages).
"""
from fractions import Fraction as Q

from laws import certificate, checked
from zeros import eps, halve


def cdf(x):
    return (x + x * x) / 2


def prefix_moments(size, k):
    """Mass and first location moment on sites 0,...,k-1, in O(1) operations."""
    linear = k * (k - 1) // 2
    quadratic = k * (k - 1) * (2 * k - 1) // 6
    # Grid site j/size carries (size + 1 + 2*j) / (2*size**2).
    mass = Q((size + 1) * k + 2 * linear, 2 * size**2)
    moment = Q((size + 1) * linear + 2 * quadratic, 2 * size**3)
    return mass, moment


def finite_ramp(ell, x, width):
    """Read the right ramp, equal to 1 at x, under a compressed grid law."""
    size = 2**ell
    lower = x * size
    upper = (x + width) * size
    first = min(size, lower.numerator // lower.denominator + 1)
    stop = min(size, -(-upper.numerator // upper.denominator))
    m0, z0 = prefix_moments(size, first)
    m1, z1 = prefix_moments(size, stop)
    return m0 + ((x + width) * (m1 - m0) - (z1 - z0)) / width


def cdf_sample(x, p):
    assert 0 <= x <= 1 and p >= 0
    d = 1  # rho <= 2**d
    width = eps(p + d + 2)
    ell = 2 * p + d + 4
    raw = finite_ramp(ell, x, width)
    # A transport error at level ell contributes <= eps(ell)/width;
    # replacing the indicator by a ramp contributes <= (2**d)*width.
    assert eps(ell) / width + (2**d) * width == eps(p+1)
    rounded = Q(round(raw * 2**p), 2**p)
    assert abs(rounded - raw) <= eps(p+1)
    return rounded


def explicit_law(ell):
    size = 2**ell
    return checked([(Q(j, size), cdf(Q(j+1, size)) - cdf(Q(j, size)))
                    for j in range(size)])


def check_compression():
    previous = None
    for ell in range(7):
        law = explicit_law(ell)
        for x in [Q(0), Q(1, 7), Q(1, 2), Q(15, 16), Q(1)]:
            for width in [Q(1, 2), Q(1, 13), Q(1, 64)]:
                dense = sum(m * min(Q(1), max(Q(0), (x + width - t)/width))
                            for t, m in law)
                assert finite_ramp(ell, x, width) == dense
        if previous is not None:
            distance, _ = certificate(previous, law)
            assert distance <= eps(ell-1) + eps(ell)
        previous = law


def check_quantile(alpha, steps):
    left, right = Q(0), Q(1)
    calls = 0

    def sample(x, p):
        nonlocal calls
        calls += 1
        value = cdf_sample(x, p)
        assert abs(value - cdf(x)) <= eps(p)
        return value - alpha

    counts = dict(left=0, middle=0, right=0)
    for j in range(steps):
        # Lower density 2**(-1) gives g(k) = k+1.
        p = (j + 2) + 1 + 1
        old_left, old_right = left, right
        left, right, direction = halve(left, right, sample, p)
        counts[direction] += 1
        assert old_left <= left < right <= old_right
        assert right - left == eps(j+1)
        assert cdf(left) <= alpha <= cdf(right)
    assert calls == steps
    return left, right, counts


if __name__ == "__main__":
    check_compression()
    for alpha in (Q(0), Q(3, 8), Q(7, 15), Q(1)):
        left, right, counts = check_quantile(alpha, 32)
        print(f"alpha={alpha}   bracket=[{left}, {right}]   branches={counts}")
    print("105 dense/compressed ramp equalities and 128 certified halvings passed.")
