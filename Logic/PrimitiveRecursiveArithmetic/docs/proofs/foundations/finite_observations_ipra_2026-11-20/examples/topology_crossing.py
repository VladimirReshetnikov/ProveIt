"""Exact clear-probe brackets for a rational path crossing the unit circle."""
from fractions import Fraction as F
from math import factorial


def displacement(t):
    return (t-F(1, 4)) * (t-F(1, 2))**3 * (t-F(3, 4))


def path(t):
    radius = 1 + displacement(t)
    return (radius * (1-t*t) / (1+t*t), radius * 2*t / (1+t*t))


def residual(t):
    x, y = path(t)
    return x*x + y*y - 1


def last_difference(values):
    row = list(values)
    while len(row) > 1:
        row = [b-a for a, b in zip(row, row[1:])]
    return row[0]


def shrink(left, right):
    degree = 10
    width = right-left
    step = width/(2*degree)
    candidates = [left+width/4+j*step for j in range(degree+1)]
    values = [residual(t) for t in candidates]
    best = max(range(len(candidates)), key=lambda j: abs(values[j]))
    probe = candidates[best]
    expected = factorial(degree) * step**degree
    assert last_difference(values) == expected
    assert abs(values[best]) >= expected / (2**degree) > 0
    assert left < probe < right
    if (residual(left) > 0) == (values[best] > 0):
        return probe, right
    return left, probe


def exercise(initial, steps):
    left, right = initial
    original_width = right-left
    roots = [F(1, 4), F(1, 2), F(3, 4)]
    for j in range(steps):
        assert residual(left)*residual(right) < 0
        old = left, right
        left, right = shrink(left, right)
        assert old[0] <= left < right <= old[1]
        assert right-left <= F(3, 4)*(old[1]-old[0])
        assert 2**((j+1)//3)*(right-left) <= original_width
        assert any(left < t < right for t in roots)
    contained = [str(t) for t in roots if left < t < right]
    assert len(contained) == 1
    denominator = int(1/(right-left))
    print(f"{initial[0]} .. {initial[1]}: {steps} certified cuts, "
          f"remaining root {contained[0]}, width at most 1/{denominator}")


if __name__ == "__main__":
    for interval in [(F(0), F(1)), (F(1, 8), F(3, 8)),
                     (F(3, 8), F(5, 8)), (F(5, 8), F(7, 8))]:
        exercise(interval, 24)
