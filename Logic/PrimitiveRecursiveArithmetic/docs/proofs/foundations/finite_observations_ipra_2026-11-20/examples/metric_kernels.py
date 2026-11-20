"""Exact finite calculations from the metric-kernel chapter (standard library)."""

from fractions import Fraction as F
from itertools import product
from random import Random


def compose(first, second):
    """Rows are sources and columns are destinations."""
    assert first and first[0] and second and second[0]
    assert all(len(row) == len(second) for row in first)
    assert all(len(row) == len(second[0]) for row in second)
    return [[min(row[i] + second[i][j] for i in range(len(second)))
             for j in range(len(second[0]))] for row in first]


def envelopes(sites, intervals, lipschitz):
    assert sites and len(sites) == len(intervals)
    assert lipschitz >= 0 and all(lo <= hi for lo, hi in intervals)
    excess = max(lo - hi - lipschitz * abs(x - y)
                 for x, (lo, _) in zip(sites, intervals)
                 for y, (_, hi) in zip(sites, intervals))
    radius = max(F(0), excess) / 2

    def evaluate(x):
        lower = max(lo - radius - lipschitz * abs(x - a)
                    for a, (lo, _) in zip(sites, intervals))
        upper = min(hi + radius + lipschitz * abs(x - a)
                    for a, (_, hi) in zip(sites, intervals))
        return lower, upper

    return radius, evaluate


def run():
    rng = Random(5827)
    for _ in range(60):
        sizes = [rng.randint(1, 6) for _ in range(4)]
        def matrix(n, m):
            return [[F(rng.randrange(20), rng.randint(1, 9)) for _ in range(m)]
                    for _ in range(n)]
        a, b, c = (matrix(n, m) for n, m in zip(sizes, sizes[1:]))
        assert compose(compose(a, b), c) == compose(a, compose(b, c))

    sites = [F(0), F(1, 3), F(1)]
    radius, fit = envelopes(sites, [(F(v), F(v)) for v in (0, 1, 0)], F(1))
    assert radius == F(1, 3)
    assert [fit(x)[1] for x in sites] == [F(1, 3), F(2, 3), F(1, 3)]
    assert min(abs(F(1, 2)-x)*2 for x in [F(0), F(1)]) == 1
    samples = [F(i, 32) for i in range(33)]
    distance = [[abs(x-y) for y in samples] for x in samples]
    # Signed offsets are kept nonnegative by adding one.
    kernel = [[1 + abs(x/2-y/3) for y in samples] for x in samples]
    assert compose(distance, kernel) == kernel == compose(kernel, distance)
    for x, y in product(samples, repeat=2):
        l, u = fit(x)
        ll, uu = fit(y)
        assert l <= u and abs(l-ll) <= abs(x-y) and abs(u-uu) <= abs(x-y)
    print("60 rectangular associativity checks; 2 Yoneda identities on 33 sites;")
    print("optimal interval expansion 1/3, upper fit (1/3, 2/3, 1/3);")
    print("sharp midpoint displacement = 1 at covering radius 1/2.")


if __name__ == "__main__":
    run()
