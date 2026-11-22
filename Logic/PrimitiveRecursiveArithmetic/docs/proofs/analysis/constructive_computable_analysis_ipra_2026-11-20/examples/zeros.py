"""Exact arithmetic regression for one-query zero isolation; Python 3 standard library."""
from collections import Counter
from fractions import Fraction as Q
from typing import Callable

Sampler = Callable[[Q, int], Q]


def eps(k: int) -> Q:
    return Q(1, 2**k)


def halve(left: Q, right: Q, sample: Sampler, p: int) -> tuple[Q, Q, str]:
    """Use one sample at a rational midpoint and two rational comparisons."""
    mid = (left + right) / 2
    e = eps(p)
    value = sample(mid, p)
    if value >= e:
        return left, mid, "left"
    if value <= -e:
        return mid, right, "right"
    return (left + mid) / 2, (mid + right) / 2, "middle"


def check(f: Callable[[Q], Q], inv: Callable[[int], int], steps: int, seed: int):
    left, right = Q(0), Q(1)
    counts = Counter()
    calls = 0
    def sample(x: Q, p: int) -> Q:
        nonlocal calls
        calls += 1
        # Cover exact observations, fractional noise, and both extreme errors.
        offset = (2 * calls + x.numerator + seed) % 5 - 2
        return f(x) + eps(p) * Q(offset, 2)
    for j in range(steps):
        old_left, old_right = left, right
        left, right, branch = halve(left, right, sample, inv(j+2)+1)
        counts[branch] += 1
        assert old_left <= left < right <= old_right
        assert right - left == eps(j+1)
        assert f(left) <= 0 <= f(right)
        assert (left * 2**(j+2)).denominator == 1
    assert calls == steps
    return left, right, counts


def exponential_sample(x: Q, p: int) -> Q:
    """Taylor reading of exp(x) - 3/2 with a rational tail bound on [0,1]."""
    term, partial = Q(1), Q(1)
    for i in range(1, p+3):
        term = term*x/i
        partial += term
    return partial-Q(3,2)


def check_log_root():
    left, right = Q(0), Q(1)
    for j in range(32):
        left, right, _ = halve(left, right, exponential_sample, j+3)
        # Independently enclose each endpoint by a finer Taylor bound.
        t = j+24
        assert exponential_sample(left,t) + eps(t) <= 0
        assert exponential_sample(right,t) >= 0
        assert right-left == eps(j+1)
    print(f"log(3/2), 32 one-query steps: [{left}, {right}]")


if __name__ == "__main__":
    models = [
        ("x + x^3 - 7/10", lambda x: x + x**3 - Q(7, 10), lambda k: k),
        ("(x - 1/3)^3", lambda x: (x-Q(1, 3))**3, lambda k: 3*k+2),
        ("x", lambda x: x, lambda k: k),
        ("x - 1", lambda x: x-1, lambda k: k),
        ("x - 1/2", lambda x: x-Q(1, 2), lambda k: k),
    ]
    total = Counter()
    for title, f, g in models:
        results = [check(f, g, 40, seed) for seed in range(5)]
        assert max(a for a, _, _ in results) <= min(b for _, b, _ in results)
        total.update(sum((c for _, _, c in results), Counter()))
        left, right, _ = results[0]
        print(f"{title}: [{left}, {right}]")
    assert set(total) == {"left", "middle", "right"}
    print(f"{sum(total.values())} steps verified: {dict(sorted(total.items()))}")
    check_log_root()
