#!/usr/bin/env python3
"""Close 67 of 71 discriminants in the five-term finite reduction.

The other four require the residue sieve.  This verifies their polynomial
coefficients as well.  Polynomial coefficient lists start with the constant.
"""
import json
import math
import sys
from fractions import Fraction
from itertools import permutations
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "cm"))
from verify_class_polynomials import reduced_forms, singular_modulus, class_polynomial
from verify_disks import check_row


def squared_radius(z):
    def limits(r):
        lo = 0 if r.lo <= 0 <= r.hi else min(abs(r.lo), abs(r.hi))
        return lo, max(abs(r.lo),abs(r.hi))
    x,X = limits(z.re)
    y,Y = limits(z.im)
    return x*x+y*y, X*X+Y*Y


def dominant(D, forms):
    valid = set(reduced_forms(D))
    assert len(forms)==5 and len(set(tuple(f) for f in forms))==5
    bounds = []
    for a,b,c in forms:
        assert (a,b,c) in valid
        z = singular_modulus(D,a,b)
        lower,upper = squared_radius(z)
        bounds.append((math.isqrt(lower), math.isqrt(upper)+1))
    assert bounds[0][0]>0
    assert all(bounds[i][1]<bounds[i+1][0] for i in range(4))
    diag = math.prod(z[0]**i for i,z in enumerate(bounds))
    permset = permutations(range(5))
    off = sum(math.prod(z[1]**i for i,z in zip(perm,bounds))
              for perm in permset if perm!=tuple(range(5)))
    return off<diag


def main():
    data=json.loads((HERE/'five_small_witnesses.json').read_text())
    expected = {int(D) for D in data}
    # Compare the precise output of the preceding exhaustive reducer if available.
    from global_five import census, reduce_survivors
    assert set(reduce_survivors(census())) == expected
    modes={}
    for D,entry in data.items():
        D=int(D)
        h=entry["class_number"]
        assert len(list(reduced_forms(D)))==h and h>=6
        if "forms" in entry:
            assert dominant(D,entry["forms"])
            method = 'archimedean'
        else:
            coeffs=class_polynomial(D,h)
            assert coeffs==entry["coefficients"]
            if 'disk' in entry:
                p,k,a,r,n=entry['disk']
                assert check_row(coeffs,5,p,k,a,Fraction(r))==n
                method='p-adic disk'
            else:
                assert D in (87,348,432,675)
                method='polynomial provided for residue sieve'
        modes[method]=modes.get(method,0)+1
    assert len(data)==71
    print(modes)


if __name__=='__main__':
    main()
