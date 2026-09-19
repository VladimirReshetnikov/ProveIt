"""Small exact checker for the finite part of the classification."""
from fractions import Fraction
from math import comb


def L(a):
    b = [0] + a + [0]
    return [b[k+1]**2 - b[k]*b[k+2] for k in range(len(a))]


def cone(a):
    return min(a) >= 0 and all(
        a[k]**2 >= 3*a[k-1]*a[k+1] for k in range(1, len(a)-1))


for n in range(3, 18):
    a = [0, n-1] + [comb(n, k) for k in range(2, n+1)]
    for j in range(6):
        bad = [(k, x) for k, x in enumerate(a) if x < 0]
        if bad:
            expected = 5 if n == 12 else 4 if n <= 16 else 3
            assert n >= 12 and j == expected and bad[0][0] == 2
            print(n, "failure", j, bad)
            break
        if cone(a):
            assert 3 <= n <= 11
            ratios = [(Fraction(a[k]**2, a[k-1]*a[k+1]), k)
                      for k in range(1, n) if a[k-1]*a[k+1]]
            print(n, "invariant cone", j, "minimum", min(ratios))
            break
        a = L(a)
    else:
        raise AssertionError((n, "no conclusion"))
