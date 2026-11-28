#!/usr/bin/env python3
"""Check finite sums, short-block bounds and a sample of the triple partition."""
from fractions import Fraction
from math import isqrt

def check_short_blocks():
    count = 0
    for n in range(1, 70):
        for k in range(isqrt(3*n*n)-n+1):
            m = k+1
            center = Fraction(2*n+k, 2)
            values = [(j-Fraction(k, 2))**2 for j in range(m)]
            mean = sum(values)/m
            variance = sum((x-mean)**2 for x in values)/m
            assert mean == Fraction(k*(k+2), 12)
            assert variance == Fraction(k*(k-1)*(k+2)*(k+3), 180)
            lower = Fraction(m*m, 2*sum((n+j)**2 for j in range(m)))
            paired = sum(1/(center**2+x) for x in values)/2
            assert lower <= paired <= lower*(1+variance/(center**2*(center**2+mean)))
            count += 1
    print(f"{count} exact short-block comparisons passed.")

def periodic_member(k, first_residue, number):
    """Elements using the residue representatives 1,...,100; k starts at 1."""
    epoch, offset = divmod(k-1, number)
    return 100*epoch+first_residue+offset

def check_partition():
    # Disjoint target residues 1..58 and 59..96 mod 100.
    low, high = 1000, 100000
    used = set()
    triples = 0
    for n in range(low, high+1):
        if n in used:
            continue
        j3 = isqrt(3*(58*n)**2)//100
        j7 = isqrt(7*(38*n)**2)//100
        p = periodic_member(j3,1,58)
        q = periodic_member(j7,59,38)
        assert n < p < q and not used.intersection((n,p,q))
        used.update((n,p,q))
        triples += 1
    assert all(n in used for n in range(low,high+1))
    print(f"{triples} disjoint triples cover [{low},{high}]; "
          "some partners lie beyond the upper endpoint.")
    assert Fraction(1,2)/(1+Fraction(1,3)+Fraction(1,7)) == Fraction(21,62)

if __name__ == '__main__':
    check_short_blocks()
    check_partition()
