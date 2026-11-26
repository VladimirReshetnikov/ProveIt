"""Rational endpoint verification for the four-term cutoff at |Delta| = 10**11."""

from fractions import Fraction as Q
from math import ceil, floor


def exp_lower(argument, terms=160):
    """Finite Taylor lower bound for the exponential of a nonnegative rational."""
    assert argument >= 0
    term = Q(1)
    total = term
    for k in range(1, terms + 1):
        term = term * argument / k
        total += term
    return total


def main():
    D = 10**11
    assert 316227**2 < D < 316228**2
    pi_lower = Q("3.14")
    log_D = Q("25.329")
    log_two = Q("0.694")
    assert exp_lower(log_D) > D and exp_lower(log_two) > 2
    data = {
        46: ("120.61", "9.586"),
        48: ("123.21", "9.628"),
        189: ("244.48", "10.999"),
        230: ("269.69", "11.195"),
        500: ("397.64", "11.972"),
    }
    errors = {0: 0}
    removals = {}
    for numerator, (sqrt_text, log_text) in data.items():
        upper_y = Q(numerator, 1000) * 316228
        sqrt_y, log_y = Q(sqrt_text), Q(log_text)
        assert sqrt_y**2 > upper_y
        assert exp_lower(log_y) > upper_y
        errors[numerator] = sqrt_y * (
            (log_y / (2 * pi_lower) + 2) * log_D
            + 2 * (log_y**2 / (8 * pi_lower) + 2)
        )
        removals[numerator] = 2 * sqrt_y * log_y + log_D + 2 * log_two
    for a, b in [(0, 46), (48, 189), (230, 500)]:
        width = floor(Q(b - a, 1000) * 316227)
        error = ceil(errors[a] + errors[b])
        removal = ceil(removals[b])
        margin = width - error - removal
        assert margin > 0
        print(f"({a}/1000,{b}/1000]: width >= {width}, errors <= {error} + {removal}, margin >= {margin}")
    for a, b in [(46, 48), (189, 230)]:
        assert pi_lower * (Q(1000, a) - Q(1000, b)) > Q("2.84")
    assert pi_lower * Q(1000, 230) > 13
    assert exp_lower(Q(13)) > 207900
    assert Q(99, 101) * exp_lower(Q("2.84")) > 16
    print("Both archimedean separation bounds exceed 16.")


if __name__ == "__main__":
    main()
