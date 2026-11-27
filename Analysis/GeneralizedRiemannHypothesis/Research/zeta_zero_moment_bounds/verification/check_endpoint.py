"""Exact endpoint certificate with a double largest value and three moments.

Run with Python 3 using its standard library. Every sign, interval bound, and
polynomial identity is verified with rational arithmetic.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import prod


def main():
    original = (Q(1), Q(1), Q(1, 2), Q(1, 4), Q(1, 8))
    powered = [x**3 for x in original]
    s1, s2, s3 = (sum(y**j for y in powered) for j in (1, 2, 3))
    e1, e2, e3 = (sum(prod(c) for c in combinations(powered, j))
                  for j in (1, 2, 3))

    # The coefficients of E(u)/(1+tu)^2 through degree three.
    def b1(t):
        return e1 - 2*t

    def b2(t):
        return e2 - 2*e1*t + 3*t**2

    def p(t):
        return e3 - 2*e2*t + 3*e1*t**2 - 4*t**3

    # For any positive spectrum with these moments and top multiplicity two,
    # s2/s1 <= largest <= s1/2. The cubic decreases on that entire interval:
    # p''(t)=6*e1-24*t < 0 there, and p' is negative at the left endpoint.
    left, right = s2/s1, s1/2
    assert 6*e1 < 24*left
    assert -2*e2 + 6*e1*left - 12*left**2 < 0
    scale = 10**10
    lo, hi = Q(10000022187, scale), Q(10000022188, scale)
    assert left < lo < hi < right and p(lo) > 0 > p(hi)
    print("k = 3, r = 2, d = 3")
    print("Powered spectrum: 1, 1, 1/8, 1/64, 1/512")
    print("Moment interval for largest value:", left, "to", right)
    print("Unique upper endpoint t in (1.0000022187, 1.0000022188)")

    # b1 decreases, while b2 increases throughout the isolating interval.
    assert 6*lo > 2*e1
    # At t, the two tail values are roots of z^2 - b1(t) z + b2(t).
    # Enclose its evaluation for every possible t in [lo, hi].
    def sign(z):
        lower = z**2 - b1(lo)*z + b2(lo)
        upper = z**2 - b1(hi)*z + b2(hi)
        if lower > 0:
            return 1
        if upper < 0:
            return -1
        raise ArithmeticError("The sign enclosure contains zero")

    brackets = [(Q(1, 128), Q(1, 32)), (Q(1, 16), Q(1, 4))]
    for a, b in brackets:
        assert 0 < a < b < lo and sign(a)*sign(b) == -1
        print(f"Distinct positive residual root in ({a}, {b})")

    # For the multiset (t,t,z1,z2), use z1+z2=b1 and z1*z2=b2.
    # The next identities have degree at most three in t. Verifying them at
    # four distinct rational points proves the identities of polynomials.
    for t in map(Q, range(4)):
        total, pair = b1(t), b2(t)
        assert 2*t + total == s1
        assert 2*t**2 + total**2 - 2*pair == s2
        assert 2*t**3 + total**3 - 3*total*pair == s3 - 3*p(t)
    print("Moment identities verified through degree 3 modulo p(t)=0.")
    # At the largest value y of any competitor, p(y) equals the nonnegative
    # third elementary symmetric sum of the tail. Since p is decreasing,
    # y <= t. The four-atom realization proves that equality is attained.
    print("The four-atom multiset (t,t,z1,z2) attains the upper endpoint.")


if __name__ == "__main__":
    main()
