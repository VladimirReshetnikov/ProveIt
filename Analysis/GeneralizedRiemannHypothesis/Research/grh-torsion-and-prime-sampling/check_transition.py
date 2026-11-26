"""Verify exact critical-budget crossings at and between score boundaries."""

from fractions import Fraction
from verify_minimax import blocking_marks, shell_size


def first_safe(p, h0, budget, tolerance, max_h):
    spent = Fraction(0)
    for h in range(h0, max_h + 1):
        spent += Fraction(blocking_marks(p, h, tolerance), shell_size(p, h))
        if spent > budget:
            return h
    return None


def main():
    checked = 0
    for p in [2, 3, 5, 7, 11]:
        for h0 in [1, 2, 4]:
            critical = Fraction(p, (p - 1) * p ** (h0 - 1))
            for first_change in range(max(3, h0 + 1), 24):
                baseline = Fraction(1, p ** (first_change - 1))
                for multiplier in (1, Fraction(1 + p, 2), Fraction(1000 * p - 1, 1000)):
                    tolerance = baseline * multiplier
                    actual = first_safe(p, h0, critical, tolerance, first_change + 2)
                    expected = first_change + (p == 2)
                    assert actual == expected, (p, h0, tolerance, actual, expected)
                    checked += 1
    print(f'PASS: {checked} critical-budget crossings, including equality at the first score.')
    example = first_safe(2, 1, Fraction(2), Fraction(1, 4), 6)
    assert example == 4
    print('PASS: the first safe cutoff for p=2, start=1, B=2, tolerance=1/4 is 4.')


if __name__ == '__main__':
    main()
