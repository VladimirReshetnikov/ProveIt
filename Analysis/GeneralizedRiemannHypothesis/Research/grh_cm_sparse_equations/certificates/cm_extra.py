#!/usr/bin/env python3
"""Certify local clusters in the 79 supplied CM class polynomials.

Run python cm_extra.py [cm-polys.json] > cm-clusters.csv.
All coefficients are listed in increasing degree in the input.
"""
from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path
import csv
import json
import sys

# A center (p, v, r) means X = p**v*(r+Z), with r a p-adic unit.
CENTERS = (
    (2, 3, 5), (2, 6, 3), (2, 6, 5),
    (3, 3, 1), (3, 3, 2),
    (7, 0, 6), (13, 0, 5), (17, 0, 8)
)

def threshold(p,t):
    """For t=4,5, a strict excess over this relative depth suffices."""
    assert t in (4,5)
    if p == 2:
        return Fraction(2)
    if p == 3:
        return Fraction(1)
    return Fraction(1,p-t+1)

def valuation(n,p):
    assert n
    v=0
    while n%p == 0:
        n//=p
        v+=1
    return v

def translate(coeff,p,v,r):
    """Coefficients of H(p**v*(r+Z)) in increasing degree."""
    scaled=[c*p**(v*i) for i,c in enumerate(coeff)]
    return [sum(scaled[j]*comb(j,i)*r**(j-i) for j in range(i,len(scaled)))
            for i in range(len(scaled))]

def certificate(coeff,p,v,r,t):
    """Count roots with v_p(Z)>threshold via the lowest minimal-weight index."""
    level=threshold(p,t)
    shifted=translate(coeff,p,v,r)
    weighted=[(valuation(c,p)+i*level,i) for i,c in enumerate(shifted) if c]
    weight,count=min(weighted)
    if count < t:
        return None
    ordinates=" ".join(str(valuation(c,p)) if c else "inf" for c in shifted)
    return (p,v,r,level,count,weight,ordinates)

def strongest(coeff):
    h=len(coeff)-1
    for t in range(h,3,-1):
        for p,v,r in CENTERS:
            cert=certificate(coeff,p,v,r,t)
            if cert:
                return (t,)+cert
    raise ValueError("No four-root certificate in the specified disks")

def main():
    fn=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('cm-polys.json')
    polynomials=json.loads(fn.read_text())
    assert len(polynomials)==79
    writer=csv.writer(sys.stdout,lineterminator='\n')
    writer.writerow(('abs_D','h','t','p','v','r','threshold','roots_in_open_disk',
                     'minimum_weight','coefficient_valuations_ascending'))
    counts=Counter()
    for key in sorted(polynomials,key=int):
        coeff=polynomials[key]
        assert coeff[-1]==1
        t,*data=strongest(coeff)
        h=len(coeff)-1
        writer.writerow((key,h,t,*data))
        counts[h,t]+=1
    assert counts=={(4,4):50,(5,4):1,(5,5):28}
    print('Certified 50 quartics and 29 quintics for t=4; 28 of the quintics for t=5.',
          file=sys.stderr)

if __name__=='__main__':
    main()
