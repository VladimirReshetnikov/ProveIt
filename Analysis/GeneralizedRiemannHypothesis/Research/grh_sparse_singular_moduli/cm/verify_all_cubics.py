#!/usr/bin/env python3
"""Independent one-disk proof of Bilu--Luca--Pizarro-Madariaga, Theorem 6.6."""
from fractions import Fraction
from math import factorial
from verify_class_polynomials import class_polynomial, reduced_forms
from verify_quintic_list import is_fundamental, prime_divisors, kronecker_at_prime
from verify_disks import shifted_coefficients, valuation

# Each key gives (p,scale,unit) in the disk above p^scale times unit.
GROUPS = {
    (2,4,3): [44,76,108,172,268,652],
    (3,3,1): [31,124,139,211,283,307,331,379,499,547,643,883,907],
    (7,0,6): [23,92,107],
    (13,0,5): [59,83],
    (17,0,8): [243],
}


def cubic_orders():
    orders=set()
    # Watkins gives fundamental-discriminant bounds 163 and 907 for h=1,3.
    for d in range(3,908):
        if not is_fundamental(-d):
            continue
        h=len(list(reduced_forms(d)))
        if h not in (1,3):
            continue
        # The order class number formula implies phi(f)<=9, hence f<=162.
        for f in range(1,163):
            m=f
            for p in prime_divisors(f):
                m=m//p*(p-kronecker_at_prime(-d,p))
            units=1 if f==1 else {3:3,4:2}.get(d,1)
            if h*m==3*units:
                orders.add(d*f*f)
    return orders


def main():
    ds={d for group in GROUPS.values() for d in group}
    assert len(ds)==25 and ds==cubic_orders()
    for (p,scale,unit),group in GROUPS.items():
        r=Fraction(1 if p<=3 else 2,1 if p<=3 else p-1)+Fraction(1,300)
        assert r>Fraction(1,p-1)
        maximum=max(i*r-valuation(factorial(i),p) for i in range(3))
        n=3
        while n*r-Fraction(n-1,p-1)<=maximum:
            assert n*r-valuation(factorial(n),p)>maximum
            n+=1
        for d in group:
            h=class_polynomial(d,3)
            shifted=shifted_coefficients(h,p,scale,unit)
            weights=[(valuation(b,p)+i*r,i) for i,b in enumerate(shifted) if b]
            assert min(weights)[1]==3
    print("All 25 class-number-three orders require exactly four terms.")


if __name__=="__main__":
    main()
