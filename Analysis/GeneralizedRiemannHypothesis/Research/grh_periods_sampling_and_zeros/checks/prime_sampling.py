"""Exact finite checks for the binary construction (standard library, Python 3).

Use a = 10^5, b = 11^5, density 1/2, eta = 1/16.  Outside [a,b] the
cumulative model is F(x)=x/2.  The bump vanishes at a and b.  The integer
counts, midpoint height, and enclosure for the centered midpoint-to-endpoint
rise are computed with integer and rational arithmetic throughout.
"""
from fractions import Fraction as Q


def model_count(x, a, b):
    """Return numerator and denominator of F(x) at an integer x."""
    if x < a or x > b:
        return x, 2
    width = b - a
    offset = x - a
    # F(x) = x/2 + (H/a)^2 x^2 f'((x-a)/H)/(16 H).
    denominator = 16 * a**2 * width**4
    correction = 3 * x**2 * offset**2 * (width-offset)**2 * (width-2*offset)
    return x * (denominator // 2) + correction, denominator


def bump(x, a, b):
    t = Q(x - a, b - a)
    return Q((b-a)**2, 16 * a**2) * t**3 * (1-t)**3


def main():
    a, b = 10**5, 11**5
    y = (a + b) // 2
    last_count = 0
    ones_in_gap = 0
    for n in range(1, b + 1):
        numerator, denominator = model_count(n, a, b)
        count, residue = divmod(numerator, denominator)
        bit = count - last_count
        assert bit == 0 or bit == 1
        assert 0 <= residue < denominator
        if n > a:
            ones_in_gap += bit
        last_count = count
    assert last_count == b // 2
    assert ones_in_gap == b // 2 - a // 2
    height = bump(y, a, b)
    # |(R(y)-B(y))-(R(b)-B(b))| <= integral_y^b 2/t^2 dt.
    error = 2 * (Q(1, y) - Q(1, b))
    assert bump(a, a, b) == bump(b, a, b) == 0
    # Also independently accumulate the actual finite R(y)-R(b). For
    # each term of the reciprocal sum use a rational fixed-point interval.
    unit = 10**24
    sum_floor = 0
    included = 0
    ny, dy = model_count(y, a, b)
    count_y = ny // dy
    previous = count_y
    for n in range(y + 1, b + 1):
        numerator, denominator = model_count(n, a, b)
        count = numerator // denominator
        if count != previous:
            sum_floor += unit // n
            included += 1
        previous = count
    # log(b/y) = 2*atanh((b-y)/(b+y)); enclose the positive series tail.
    z = Q(b-y, b+y)
    terms = 16
    log_lower = 2 * sum(z**(2*k+1) / (2*k+1) for k in range(terms))
    log_upper = log_lower + 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    offset = Q(last_count, b) - Q(count_y, y)
    actual_lower = offset + log_lower/2 - Q(sum_floor + included, unit)
    actual_upper = offset + log_upper/2 - Q(sum_floor, unit)
    assert 0 < height-error <= actual_lower <= actual_upper <= height+error
    print(f'Grid endpoints {a} and {b}, interior point {y}')
    print(f'Checked binary increments on {b} integers; ones in gap: {ones_in_gap}')
    print(f'B(interior) = {height}')
    print(f'Bound for centered increment error = {error}')
    scale = 10**12
    lo = (actual_lower * scale).__floor__()
    hi = (actual_upper * scale).__ceil__()
    print(f'Actual centered increment in [{lo}, {hi}] / {scale}')
    print('All assertions passed (integer and rational arithmetic).')


if __name__ == '__main__':
    main()
