#!/usr/bin/env python3
"""High-precision diagnostics, not interval certificates (mpmath required)."""
from __future__ import annotations
import csv,json
from pathlib import Path
from math import factorial,prod
import mpmath as mp
from coefficients import coefficients
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=90

def main():
    refs=json.loads((ROOT/'data/oeis_selected.json').read_text())
    rows=[]
    for name in ('A181198','A181199'):
        entry=refs[name]; m=entry['height'];d=m*(m-1)//2
        alpha=mp.mpf(m*m-1)/2
        K=mp.sqrt(m)*mp.power(2*mp.pi,mp.mpf(1-m)/2)*prod(factorial(j) for j in range(m))/4**d
        c,b=coefficients(m,5)
        for n in (10,20,40,80):
            a=mp.mpf(entry['terms'][str(n)])
            lead=K*mp.power(m,m*n)*mp.power(n,-alpha)
            ratio=a/lead
            errors={}
            for J in (0,1,2,5):
                partial=sum(mp.mpf(b[j].numerator)/b[j].denominator/mp.mpf(n)**j for j in range(J+1))
                errors[str(J)]=mp.nstr(lead*partial/a-1,18)
            rows.append({'sequence':name,'n':n,'exact_over_leading':mp.nstr(ratio,18),
                         **{'relative_error_J'+j:v for j,v in errors.items()},
                         'exact_value_source':'independent DP + OEIS' if n<=40 else 'OEIS input only'})
    with (ROOT/'data/numerics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
