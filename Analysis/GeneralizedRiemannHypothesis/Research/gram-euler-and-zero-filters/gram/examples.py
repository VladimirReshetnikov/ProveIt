"""Construct integer test matrices and compute their Gram determinants exactly."""
from fractions import Fraction
from math import gcd
import json

T = Fraction("6.34926542772847")
C = Fraction("0.4787974286905903")


def columns(n):
    """Select n representatives from the six-row ellipse, using rational comparisons."""
    r_squared = (n - 1) / (2 * C)
    a_fourth = (T * T / r_squared) ** 2
    u, v = a_fourth.numerator, a_fourth.denominator
    candidates = [(u, 1, 0)]
    for j in range(1, 7):
        candidates.extend((u * m * m + v * j * j, m, j)
                          for m in range(-n, n + 1) if gcd(m, j) == 1)
    return [(m, j) for _, m, j in sorted(candidates)[:n]]


def summarize(n):
    points = columns(n)
    assert (1, 0) in points and any(j == 1 for _, j in points)
    assert len(set(points)) == n and all(gcd(x, y) == 1 for x, y in points)
    xx = sum(x * x for x, _ in points)
    xy = sum(x * y for x, y in points)
    yy = sum(y * y for _, y in points)
    energy = xx * yy - xy * xy
    if n <= 100:
        squares = [(x * v - y * u) ** 2 for i, (x, y) in enumerate(points)
                   for u, v in points[i+1:]]
        assert min(squares) > 0 and sum(squares) == energy
    return dict(n=n, gram=[[xx, xy], [xy, yy]], energy=energy,
                normalized=energy / (n - 1) ** 4,
                counts=[sum(j == k for _, j in points) for k in range(7)])


if __name__ == "__main__":
    print(json.dumps([summarize(n) for n in [20, 100, 1000, 10000]], indent=2))
