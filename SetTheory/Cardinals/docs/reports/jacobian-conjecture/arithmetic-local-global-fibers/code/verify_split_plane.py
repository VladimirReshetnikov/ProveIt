#!/usr/bin/env python3
"""Exact checks for the split-root plane classification (standard library only)."""
from __future__ import annotations
import json
from fractions import Fraction
from math import gcd, pi
from pathlib import Path
from verify_finite import F

def split_data(a: int,b: int):
    c=1-a-b
    roots=(a,b,c)
    if len(set(roots))<3:
        raise ValueError('Repeated roots are excluded')
    ds=tuple((r-roots[(i+1)%3])*(r-roots[(i+2)%3]) for i,r in enumerate(roots))
    points=tuple((Fraction(1,d),r-d,5*d*d-3*r*d-2*d**3)
                 for r,d in zip(roots,ds))
    return roots,ds,points,(a*b*c,2*(a*b+a*c+b*c),2)

def main():
    checked=0
    for a in range(-20,21):
        for b in range(-20,21):
            if len({a,b,1-a-b})<3:
                continue
            roots,ds,pts,target=split_data(a,b)
            assert all(F(*pt)==target for pt in pts)
            assert all(abs(d)>1 for d in ds)
            g=gcd(a-b,3*a-1)
            assert gcd(gcd(ds[0],ds[1]),ds[2])==g*g
            checked+=1
    counts=[]
    for H in (10,25,50,100,250):
        admissible=sum(len({a,b,1-a-b})==3 and gcd(a-b,3*a-1)==1
                       for a in range(-H,H+1) for b in range(-H,H+1))
        counts.append({'H':H,'distinct_locally_soluble':admissible,
                       'parameter_pairs':(2*H+1)**2,
                       'proportion':admissible/(2*H+1)**2})
    report={'status':'PASS','exact_fiber_checks':checked,'density_counts':counts,
            'proven_limiting_density':'27/(4*pi^2)',
            'limiting_density_decimal':27/(4*pi*pi)}
    out=Path(__file__).resolve().parents[1]/'certificates'/'split_plane_checks.json'
    out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('PASS:',checked,'split fibers; exact gcd(D_1,D_2,D_3)=g^2 and no integral point')
    print('H | admissible distinct ordered pairs | fraction of square')
    for row in counts:
        print(row['H'],row['distinct_locally_soluble'],row['proportion'])
    print('Theorem density:',report['proven_limiting_density'],'=',report['limiting_density_decimal'])

if __name__=='__main__':
    main()
