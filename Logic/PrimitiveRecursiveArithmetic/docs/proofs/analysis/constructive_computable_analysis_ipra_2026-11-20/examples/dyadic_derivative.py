"""Reconstruct a derivative from value queries with a certified Dini schedule.

Exact rational arithmetic. schedule(k) supplies a level at which
b(n) + 2*T(n) <= 2**(-k). The caller provides the proved certificate.
Run directly to replay the square and the corner tests.
"""
from fractions import Fraction as Q
from typing import Callable

Observer = Callable[[Q, int], Q]
Schedule = Callable[[int], int]


def eps(k: int) -> Q:
    return Q(1, 1 << k)


def value_slope(value: Observer, x: Q, n: int, p: int) -> Q:
    if not 0 <= x <= 1:
        raise ValueError("argument outside [0, 1]")
    count = 1 << n
    index = min(count - 1, (count * x.numerator) // x.denominator)
    left = Q(index, count)
    right = Q(index + 1, count)
    return count * (value(right, p) - value(left, p))


def derivative(value: Observer, schedule: Schedule, x: Q, k: int) -> Q:
    n = schedule(k + 2)
    return value_slope(value, x, n, n + k + 3)


def derivative_at_name(value: Observer, schedule: Schedule,
                       argument: Callable[[int], Q], k: int) -> Q:
    n = schedule(k + 2)
    x = max(Q(0), min(Q(1), argument(n + 1)))
    return value_slope(value, x, n, n + k + 3)


def rounded_square(x: Q, p: int) -> Q:
    return Q((x * x) // eps(p)) * eps(p)


def square_schedule(k: int) -> int:
    # b(n)=2*h and T(n)=h, so b(n)+2*T(n)=4*h.
    return k + 2


def checks() -> None:
    samples = 0
    for k in range(9):
        for j in range(38):
            x = Q(j, 37)
            inputs = []

            def read(z: Q, p: int) -> Q:
                inputs.append((z, p))
                return rounded_square(z, p)

            approx = derivative(read, square_schedule, x, k)
            assert abs(approx - 2 * x) <= eps(k)
            assert len(inputs) == 2
            arg_calls = []

            def argument(p: int) -> Q:
                arg_calls.append(p)
                return x + eps(p)

            named = derivative_at_name(rounded_square, square_schedule, argument, k)
            assert abs(named - 2 * x) <= eps(k)
            assert len(arg_calls) == 1
            samples += 1

    detail_tests = 0
    for n in range(1, 8):
        h = eps(n)
        for p in (0, 2, 7, 15):
            for j in range(1, 1 << n):
                left, mid, right = [rounded_square(i * h, p)
                                    for i in (j - 1, j, j + 1)]
                assert abs(right - 2 * mid + left) <= 2 * h * h + 4 * eps(p)
                detail_tests += 1

    # The two neighboring slopes at the old dyadic knot remain separated.
    corner = lambda z, _p: abs(z - Q(1, 2))
    for n in range(1, 12):
        left = value_slope(corner, Q(1, 2) - eps(n + 1), n, 0)
        right = value_slope(corner, Q(1, 2), n, 0)
        assert (left, right) == (-1, 1)
    print(f"passed {samples} rational and named comparisons, "
          f"{detail_tests} rounded second differences and 11 corner levels")


if __name__ == "__main__":
    checks()
