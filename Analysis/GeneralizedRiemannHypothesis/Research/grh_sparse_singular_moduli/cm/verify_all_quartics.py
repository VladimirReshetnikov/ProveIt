#!/usr/bin/env python3
"""Complete the class-number-four census with absolute-value determinant tests."""
from itertools import permutations
from math import prod
from pathlib import Path
import json
from verify_class_polynomials import reduced_forms, singular_modulus
from verify_quintic_list import is_fundamental, prime_divisors, kronecker_at_prime

HERE = Path(__file__).resolve().parent


def quartic_orders():
    # Watkins: for h_K=1,2,4 the largest |D_K| are 163,427,1555.
    bases = []
    for d in range(3,1556):
        if is_fundamental(-d):
            h = len(list(reduced_forms(d)))
            if h in (1,2,4):
                bases.append((-d,h))
    assert len(bases)==9+18+54
    out = set()
    for D,h in bases:
        # phi(f) <= 12 and f <= 2 phi(f)^2.
        for f in range(1,289):
            m=f
            for p in prime_divisors(f):
                m=m//p*(p-kronecker_at_prime(D,p))
            units=1 if f==1 else {-3:3,-4:2}.get(D,1)
            if h*m==4*units:
                out.add(D*f*f)
    return out


def passes_determinant(D):
    intervals = []
    for a,b,c in reduced_forms(-D):
        # Boundary reduced forms have real j: conjugation fixes their class.
        assert b==0 or b==a or a==c
        z=singular_modulus(-D,a,b)
        assert z.im.lo<=0<=z.im.hi
        lo,hi=z.re.lo,z.re.hi
        assert lo>0 or hi<0
        intervals.append((min(abs(lo),abs(hi)),max(abs(lo),abs(hi))))
    intervals.sort()
    assert len(intervals)==4
    assert all(intervals[i][1]<intervals[i+1][0] for i in range(3))
    ident=tuple(range(4))
    # All terms have total exponent 6 so the common dyadic scale cancels.
    diagonal=prod(intervals[i][0]**i for i in range(4))
    offdiag=sum(prod(intervals[i][1]**k for i,k in enumerate(perm))
                for perm in permutations(ident) if perm!=ident)
    return diagonal>offdiag


def main():
    known={int(D) for D,c in json.loads((HERE/"class_polynomials.json").read_text()).items() if len(c)==5}
    full=quartic_orders()
    assert len(full)==84 and known<=full and len(known)==50
    remainder=sorted(full-known)
    assert all(passes_determinant(D) for D in remainder)
    print("Watkins plus the order formula gives 84 quartic orders.")
    print("All 34 outside the 50 p-adic certificates pass the archimedean determinant test.")
    print("Additional 34:", ", ".join(map(str, sorted(map(abs,remainder)))))


if __name__=="__main__":
    main()
