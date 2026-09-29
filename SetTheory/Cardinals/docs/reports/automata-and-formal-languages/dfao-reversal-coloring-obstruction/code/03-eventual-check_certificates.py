#!/usr/bin/env python3
"""Independent checker of finite_certificates.csv; imports no producer code.

Uses onto-map inclusion-exclusion instead of Stirling recurrence, and an
integer-partition dynamic program instead of the closed product bound.
"""
from __future__ import annotations
import csv
import json
from functools import cache
from math import comb, gcd
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

@cache
def proper(q: int, x: int, y: int) -> int:
    return sum(comb(q,i)*sum((-1)**j*comb(i,j)*(i-j)**x
               for j in range(i+1))*(q-i)**y for i in range(1,q))

def main() -> None:
    rows=list(csv.DictReader((ROOT/'results/finite_certificates.csv').open()))
    pairs={(int(r['n']),int(r['k'])) for r in rows}
    expected={(n,k) for n in range(7,101) for k in range(3,min(n,13))}
    if pairs!=expected or len(rows)!=len(expected):
        raise ValueError('missing, duplicate, or unexpected certificate rows')
    bound=[1]*101
    for r in range(1,101):
        bound[r]=max(j*bound[r-j] for j in range(1,r+1))
    accepted=0
    for rec in rows:
        n,q=int(rec['n']),int(rec['k'])
        # Brute enumeration of feasible splits rather than a residue formula.
        a,b=min(((x,n-x) for x in range(2,n//2+1) if gcd(x,n-x)==1),
                key=lambda z:z[1]-z[0])
        target=proper(q,a,b)-(b if q==3 else a*b)
        candidates=[q**n-(q-1)**n,q**(n-1),(q-1)**2*q**(n-2)-1]
        for residual in range(n-1):
            support=n-residual
            for ell in range(2,support+1):
                if support%ell==0:
                    multiplicity=support//ell
                    color=((q-1)**ell+(-1)**ell*(q-1))**multiplicity*q**residual
                    candidates.append(color-support*bound[residual])
            for x in range(1,support//2+1):
                y=support-x;d=gcd(x,y)
                color=proper(q,x//d,y//d)**d*q**residual
                period=y if q==3 and d==1 else x*y//d
                candidates.append(color-period*bound[residual])
        lower=min(candidates)
        if (target!=int(rec['candidate_defect']) or lower!=int(rec['universal_lower_bound'])
            or lower!=target or int(rec['certifies_equality'])!=1):
            raise ValueError(f'certificate rejected at n={n}, k={q}')
        accepted+=1
    report={'accepted':accepted,'rejected':0,'imports_producer':False,
            'chromatic_method':'onto-map inclusion-exclusion',
            'residual_order_method':'integer-partition maximum-product dynamic program',
            'scope':'Checks the finite bound arithmetic; not the infinite theorem or a proof-assistant formalization.'}
    (ROOT/'results/independent_check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
