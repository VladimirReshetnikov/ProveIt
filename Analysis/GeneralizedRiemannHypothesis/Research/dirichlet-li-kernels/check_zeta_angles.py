#!/usr/bin/env python3
"""Enclose the zeta two-jump example using Python's exact rationals.

Input: the first 24 decimal places in Andrew Odlyzko's table of the
first 100 zeta zero ordinates (source states over 1000 decimal places).
https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros2
https://www-users.cse.umn.edu/~odlyzko/zeta_tables/index.html

This check propagates the published input intervals. It does not locate
or enumerate zeros independently. It needs only the Python standard library.
"""

from fractions import Fraction as F

ORDINATES = (
    '14.134725141734693790457251',
    '21.022039638771554992628479',
    '25.010857580145688763213790',
    '30.424876125859513210311897',
    '32.935061587739189690662368',
    '37.586178158825671257217763',
    '40.918719012147495187398126',
    '43.327073280914999519496122',
)


def atan_bounds(x):
    """The alternating-series test gives a strict surrounding interval."""
    assert 0 < x < 1
    upper = sum((-1)**k * x**(2*k + 1) / (2*k + 1) for k in range(9))
    lower = upper - x**19 / 19
    return lower, upper


def angle_from_ordinate(prefix):
    unit = F(1, 10**24)
    # Pad the truncated prefix on both sides to include the table error.
    lo, hi = F(prefix) - unit, F(prefix) + 2*unit
    return 2*atan_bounds(1/(2*hi))[0], 2*atan_bounds(1/(2*lo))[1]


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def subtract(x, y):
    return x[0] - y[1], x[1] - y[0]


def show(name, interval, digits=20):
    scale = 10**digits
    lo = interval[0]*scale
    hi = interval[1]*scale
    outward_lo = lo.numerator // lo.denominator
    outward_hi = -(-hi.numerator // hi.denominator)
    def fmt(n):
        q, r = divmod(n, scale)
        return f'{q}.{r:0{digits}d}'
    print(f'{name}: [{fmt(outward_lo)}, {fmt(outward_hi)}]')


def main():
    angles = [angle_from_ordinate(n) for n in ORDINATES]
    assert all(x[0] > y[1] for x, y in zip(angles, angles[1:]))
    a, b, c, _, _, _, seventh, eighth = angles
    repeated = add(b, b)
    mixed = add(a, seventh)
    assert add(a, eighth)[1] < repeated[0] < repeated[1] < mixed[0]
    assert repeated[0] > a[1]
    assert add(b, c)[1] < repeated[0]
    gap = subtract(mixed, repeated)
    assert F('0.00003542639') < gap[0] < gap[1] < F('0.00003542640')
    # Archimedes' rational enclosure 223/71 < pi < 22/7.
    assert 44*a[1] < F(223, 71) and 45*a[0] > F(22, 7)
    for name, interval in [('a1', a), ('a2', b), ('a3', c), ('2 a1', add(a,a)),
                           ('a1 + a2', add(a,b)), ('2 a2', repeated),
                           ('a1 + a7', mixed), ('separation', gap)]:
        show(name, interval)


if __name__ == '__main__':
    main()
