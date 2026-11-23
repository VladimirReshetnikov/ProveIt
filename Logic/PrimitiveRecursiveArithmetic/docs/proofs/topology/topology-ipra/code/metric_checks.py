"""Exact rational regression checks for the metric constructions in metric.tex.

Run with Python 3. All comparisons use Fraction. Radial tests select rational
vectors whose Euclidean norms are rational, so no tolerance or floating-point
calculation enters the inverse or Lipschitz checks. These are finite examples.
"""

from fractions import Fraction as Q
from itertools import product
from math import isqrt


def eps(k):
    return Q(1, 2**k)


def supnorm(vector):
    return max(map(abs, vector), default=Q(0))


def distance(left, right):
    return supnorm(tuple(x - y for x, y in zip(left, right)))


def scale(factor, vector):
    return tuple(factor * v for v in vector)


def exact_norm(vector):
    square = sum((v * v for v in vector), Q(0))
    num, den = isqrt(square.numerator), isqrt(square.denominator)
    return Q(num, den) if num * num == square.numerator and den * den == square.denominator else None


def radial(vector, inverse=False):
    a, s = supnorm(vector), exact_norm(vector)
    assert s is not None
    if not a:
        return vector
    return scale(s / a if inverse else a / s, vector)


def check_radial():
    pairs = 0
    for dim, radius in [(1, 5), (2, 5), (3, 3)]:
        vectors = [tuple(Q(n, 3) for n in v)
                   for v in product(range(-radius, radius + 1), repeat=dim)]
        vectors = [v for v in vectors if exact_norm(v) is not None]
        images = [(v, radial(v), radial(v, inverse=True)) for v in vectors]
        for v, forward, backward in images:
            assert radial(forward, inverse=True) == v
            assert radial(backward) == v
            assert exact_norm(forward) == supnorm(v)
            assert supnorm(backward) == exact_norm(v)
            for w, forward_w, backward_w in images:
                delta = distance(v, w)
                assert distance(forward, forward_w) <= (dim + 2) * delta
                assert distance(backward, backward_w) <= 3 * dim * delta
                pairs += 1
    return pairs


def check_stereographic():
    checks = 0
    for dimension in (1, 2, 3):
        for indices in product(range(-3, 4), repeat=dimension):
            coords = tuple(Q(i, 2) for i in indices)
            square_sum = sum(v * v for v in coords)
            for sign in (1, -1):
                v = scale(2 / (1 + square_sum), coords)
                z = sign * (square_sum - 1) / (1 + square_sum)
                assert sum(x * x for x in v) + z * z == 1
                gap = 1 - sign * z
                assert gap == 2 / (1 + square_sum) and gap > 0
                assert scale(1 / gap, v) == coords
                # Both chart choices remain valid at the equator.
                if z == 0:
                    assert scale(1 / (1 + sign * z), v) == coords
                checks += 1
    return checks


def check_completion():
    limit = Q(2, 7)

    def row(i, p):
        return limit + eps(i) + (-1)**p * eps(p)

    def diag(p):
        return row(p + 1, p + 1)

    for p, q in product(range(11), repeat=2):
        assert abs(diag(p) - diag(q)) <= eps(p) + eps(q)
        for k in range(7):
            for i in range(k, 12):
                assert abs(row(i, p) - diag(q)) <= eps(k) + eps(p) + eps(q)


def check_extension():
    # The point has two names, distinguished by the signs of their sample errors.
    x = Q(4, 11)
    for p, q in product(range(11), repeat=2):
        def output(precision, sign):
            # A(u,s) = 2u + (-1)^s 2^-s, with modulus mu(k) = k+1.
            n = 1 + max(precision, precision + 2)
            u = x + sign * eps(n)
            s = precision + 1
            return 2 * u + (-1)**s * eps(s)

        assert abs(output(p, 1) - output(q, -1)) <= eps(p) + eps(q)
        assert abs(output(p, 1) - 2 * x) <= eps(p)


def check_optimization_and_grids():
    peak = Q(3, 7)

    def value(x):
        return 1 - abs(x - peak)

    for p in range(7):
        # This 1-Lipschitz map has nu(k) = k+1 under the general extension bound.
        s = p + 2
        denom = 2**(s + 1 + 2)
        grid = [Q(i, denom) for i in range(denom + 1)]
        samples = [value(g) + (-1)**i * eps(s) for i, g in enumerate(grid)]
        maximum = max(samples)
        optimizer = grid[samples.index(maximum)]
        assert 1 <= maximum + 2 * eps(s)
        assert maximum <= value(optimizer) + eps(s)
        assert 1 <= value(optimizer) + eps(p)
        for j in range(48):
            x = Q(j, 47)
            g = Q((x * denom).__floor__(), denom)
            assert 0 <= x - g < Q(1, denom)


def check_intermediate_values():
    target = Q(7, 13)
    for p in range(9):
        s = p + 2
        # F(t)=t-target, mu(k)=k. Use nonmonotone sample errors.
        count = 2**s
        samples = [Q(i, count) - target + (-1)**i * eps(s) for i in range(count + 1)]
        if samples[0] >= 0:
            first = 0
        elif samples[-1] < 0:
            first = count
        else:
            first = next(i for i, v in enumerate(samples) if v >= 0)
        assert abs(Q(first, count) - target) <= eps(p)
    # Rational-trace exact bisection for x^2=1/2, with no square-root oracle.
    lo, hi = Q(0), Q(1)
    for p in range(31):
        assert lo * lo <= Q(1, 2) <= hi * hi
        assert hi - lo == eps(p)
        mid = (lo + hi) / 2
        if mid * mid >= Q(1, 2):
            hi = mid
        else:
            lo = mid


if __name__ == '__main__':
    check_completion()
    check_extension()
    check_optimization_and_grids()
    check_intermediate_values()
    chart_points = check_stereographic()
    pairs = check_radial()
    print(f"Metric checks passed, including {pairs} exact radial Lipschitz pairs and {chart_points} chart inversions.")
