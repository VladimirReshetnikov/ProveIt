#!/usr/bin/env python3
"""Reproduce finite lower-root brackets and the certified term bounds."""
from __future__ import annotations
import csv, json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from certify_upper_bound import upper_coefficients

HERE=Path(__file__).resolve().parent

def bracket(b:list[int],m:int,steps:int=80)->tuple[Fraction,Fraction]:
    low,high=Fraction(1),Fraction(3)
    for _ in range(steps):
        mid=(low+high)/2;z=1/mid
        f=z+sum(b[n-1]*z**(n+2) for n in range(1,m+1))-1
        if f>0:low=mid
        else:high=mid
    return low,high

def decimal_string(q:Fraction)->str:
    with localcontext() as ctx:
        ctx.prec=35
        return str(Decimal(q.numerator)/Decimal(q.denominator))

def main()->None:
    data=HERE/'data'
    meta=json.loads((data/'verification_results.json').read_text())
    b=meta['birth_counts_by_assigned_cost']
    counts=meta['sample_counts_at_most_n']
    u=upper_coefficients(29,mode=3)
    cumulative=0
    with (data/'term_bounds.csv').open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['n','certified_lower_bound','certified_upper_bound',
                         'equality_certified','assigned_birth_count'])
        for n,c in enumerate(counts,1):
            cumulative+=u[n+1]
            writer.writerow([n,c,cumulative,c==cumulative,b[n-1]])
    rows=[]
    for m in [4,8,12,16,20,24,28]:
        lo,hi=bracket(b,m)
        rows.append({'maximum_assigned_symbol_cost':m,
                     'lower_endpoint':str(lo),'upper_endpoint':str(hi),
                     'lower_decimal_display':decimal_string(lo),
                     'upper_decimal_display':decimal_string(hi)})
    (data/'finite_lower_roots.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows,indent=2))

if __name__=='__main__':main()
