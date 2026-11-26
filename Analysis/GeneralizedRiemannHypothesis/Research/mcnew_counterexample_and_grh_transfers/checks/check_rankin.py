"""Finite sanity check on the small-prime analogue of the analytic counterexample.

Natural-density gain for the much larger prime set in the theorem follows from
Euler divergence and the symbolic estimates. No numerical positivity for these
small test sets is required. This program directly tests geometric progressions
in truncated exponent boxes and the stated deletion-weight majorant.
"""
from fractions import Fraction
from itertools import product
from math import prod


def good_exponent(e):
    while e:
        e, digit = divmod(e, 3)
        if digit == 2:
            return False
    return True


def verify(primes, bound):
    dimensions = len(primes)
    grid = product(range(bound + 1), repeat=dimensions)
    old = {v for v in grid if all(map(good_exponent, v))}
    added = {tuple(2 if i in (0,j) else 1 for i in range(dimensions))
             for j in range(1, dimensions)}
    def deleted(v):
        odd = v[1:]
        exceptions = [x for x in odd if x != 1]
        return not exceptions or len(exceptions)==1 and exceptions[0]>=3
    removed = {v for v in old if deleted(v)}
    new = old - removed | added
    for b in new:
        for a in new:
            if a >= b:
                continue
            c = tuple(2*y-x for x, y in zip(a, b))
            assert c not in new, (a,b,c)
    P = prod(primes)
    weight = lambda v: Fraction(P,prod(p**e for p,e in zip(primes,v)))
    assert sum(map(weight, added)) == sum(Fraction(1,2*q) for q in primes[1:])
    assert sum(map(weight, removed)) <= 4*(1+sum(Fraction(1,q*(q-1)) for q in primes[1:])) <= 6
    print(f"Primes {primes}, full cube 0..{bound}, {len(new)} survivors, no progression")


if __name__ == '__main__':
    verify((2,3,5),12)
    verify((2,5,7,11),6)
