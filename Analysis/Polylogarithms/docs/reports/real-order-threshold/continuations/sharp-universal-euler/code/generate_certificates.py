#!/usr/bin/env python3
"""Regenerate frozen certificates; exact acceptance, Decimal proposals only."""
from __future__ import annotations
from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path
import json,time
from exact_core import require,check_polynomial_identities,polynomial_certificates,euler_axis_interval
ROOT=Path(__file__).resolve().parents[1]

def power_brackets(b:F,n:int,digits:int)->list[int]:
    grid=10**digits; big=grid**b.denominator; out=[]
    with localcontext() as ctx:
        ctx.prec=digits+35
        exponent=-Decimal(b.numerator)/Decimal(b.denominator)
        for m in range(1,2*n-1):
            r=int((exponent*Decimal(m).ln()).exp()*Decimal(grid))
            np=m**b.numerator
            # Candidate rounding is not trusted: integer inequalities accept it.
            corrections=0
            while r**b.denominator*np>big:
                r-=1;corrections+=1
                require(corrections<10,'Decimal proposal too far from bracket')
            while (r+1)**b.denominator*np<=big:
                r+=1;corrections+=1
                require(corrections<10,'Decimal proposal too far from bracket')
            out.append(r)
    return out

def main()->None:
    started=time.time();check_polynomial_identities()
    poly=polynomial_certificates()
    (ROOT/'data/bernstein_certificates.json').write_text(json.dumps(poly,indent=2)+'\n')
    print('Polynomial certificates generated:', {k:v['minimum'] for k,v in poly.items()},flush=True)
    rows=[];n=48;digits=30
    for b in [F(13021,10000),F(6511,5000),F(13023,10000)]:
        t=time.time();roots=power_brackets(b,n,digits)
        lo,hi=euler_axis_interval(b,n,10**digits,roots,verify_roots=False)
        rows.append({'b':str(b),'N':n,'digits':digits,'lower_power_numerators':list(map(str,roots)),
                     'C_lower':str(lo),'C_upper':str(hi)})
        print('Axis',b,'C in',float(lo),float(hi),'seconds',round(time.time()-t,2),flush=True)
    output={'method':'Exact integer power brackets; axis Euler error (9/8)2^-N',
            'points':rows,'b_star_lower':'13021/10000','b_star_upper':'13023/10000',
            'C_star_lower':'11365611033/10000000000',
            'C_star_upper':'5682805523/5000000000',
            'curvature_bound':'1','grid_spacing':'1/10000'}
    (ROOT/'data/axis_certificates.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Generation completed in',round(time.time()-started,2),'seconds')
if __name__=='__main__':main()
