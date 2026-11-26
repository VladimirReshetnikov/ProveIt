"""Verify the cyclotomic shell construction with exact rational arithmetic."""

from fractions import Fraction
from math import inf


def chosen_k(h, epsilon):
    return next(k for k in range(1, h + 1)
                if Fraction(k, 2 ** (h - k)) > epsilon)


def valuation_of_difference(a, b, h):
    difference = (a - b) % (2 ** h)
    if difference == 0:
        return inf
    return Fraction(difference & -difference, 2 ** (h - 1))


def exact_small_shells(max_h):
    cases = 0
    for h in range(1, max_h + 1):
        for k in range(1, h + 1):
            roots = range(1, 2 ** k, 2)
            cost = Fraction(1, 2 ** (h - k))
            # Symmetry is deliberately unused to check the congruence count.
            observed = min(sum(valuation_of_difference(a, b, h) for a in roots)
                           for b in range(1, 2 ** h, 2))
            expected = inf if k == h else (k + 1) * cost
            assert observed == expected, (h, k, observed, expected)
            cases += 1
    return cases


def check_budget(horizon, epsilon):
    total = Fraction()
    harmonic = Fraction()
    for h in range(1, horizon + 1):
        k = chosen_k(h, epsilon)
        cost = Fraction(1, 2 ** (h - k))
        assert k * cost > epsilon
        total += cost
        if h > 1:
            harmonic += Fraction(1, h - 1)
        assert total <= 2 + 4 * epsilon * harmonic
    return total


if __name__ == "__main__":
    cases = exact_small_shells(9)
    print(f"Exact minima verified for all {cases} pairs 1 <= k <= h <= 9.")
    for epsilon in (Fraction(1, 2), Fraction(1, 8), Fraction(1, 32)):
        budget = check_budget(256, epsilon)
        print(f"epsilon={epsilon}, H=256: B={budget} ({float(budget):.6f})")
