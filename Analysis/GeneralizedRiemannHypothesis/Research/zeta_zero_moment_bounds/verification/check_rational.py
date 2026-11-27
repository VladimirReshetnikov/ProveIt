"""Reproduce the paper's finite multiset experiment; Python 3 standard library.

All root isolation and inequalities use rational arithmetic. Decimal display
is used only after the enclosing rational intervals have been verified.
"""
from fractions import Fraction as Q
from math import comb


def coefficients(moments, order, mult):
    e = [Q(1)]
    for j in range(1, order + 1):
        e.append(sum((-1)**(i-1) * moments[i] * e[j-i]
                     for i in range(1, j + 1)) / j)
    return [(-1)**j * comb(mult + j - 1, j) * e[order-j]
            for j in range(order + 1)]


def evaluate(poly, t):
    value = Q(0)
    for coef in reversed(poly):
        value = value * t + coef
    return value


def nearest_root(poly, center, bits):
    # A symmetric interval about the selection point isolates the nearest root
    # provided its derivative has fixed sign and its endpoint values straddle 0.
    deriv = [j * poly[j] for j in range(1, len(poly))]
    shifted_deriv = [
        sum(comb(j, i) * deriv[j] * center**(j-i)
            for j in range(i, len(deriv))) for i in range(len(deriv))
    ]
    for shift in range(2, 24):
        delta = center / 2**shift
        error = sum(abs(coef) * delta**i
                    for i, coef in enumerate(shifted_deriv) if i)
        left, right = center - delta, center + delta
        if (error < abs(shifted_deriv[0]) and
                evaluate(poly, left) * evaluate(poly, right) < 0):
            break
    else:
        raise ValueError("Could not certify root isolation around selector")
    sign = 1 if evaluate(poly, left) > 0 else -1
    for _ in range(bits):
        mid = (left + right) / 2
        check = sign * evaluate(poly, mid)
        if check == 0:
            return mid, mid
        if check > 0:
            left = mid
        else:
            right = mid
    return left, right


def main():
    spectrum = [Q(1), Q(1), Q(1, 2), Q(1, 2), Q(1, 2), Q(1, 3), Q(1, 4)]
    print("k   h    d=1             d=2             d=3             d=4")
    for k in (8, 16, 32):
        moments = [None] + [sum(x**(j*k) for x in spectrum) for j in range(1, 5)]
        h = moments[1]**2 // moments[2]
        assert h == 2
        scaled = []
        for d, b, count in ((1, Q(1, 2), 3), (2, Q(1, 4), 3),
                             (3, Q(1, 8), 1), (4, Q(1, 24), 1)):
            poly = coefficients(moments, d, h)
            lo, hi = nearest_root(poly, moments[1]/h, bits=256)
            normalizer = Q((-1)**(d+1) * h, count) / b**k
            bounds = sorted([(lo-1) * normalizer, (hi-1) * normalizer])
            assert bounds[0] > 0
            assert bounds[1] - bounds[0] < Q(1, 10**18)
            # Check the full enclosure agrees to 9 decimal places.
            pair = [f"{float(x):.9f}" for x in bounds]
            assert pair[0] == pair[1]
            scaled.append(pair[0])
        print(f"{k:2}  {h:2}    " + "     ".join(scaled))


if __name__ == "__main__":
    main()
