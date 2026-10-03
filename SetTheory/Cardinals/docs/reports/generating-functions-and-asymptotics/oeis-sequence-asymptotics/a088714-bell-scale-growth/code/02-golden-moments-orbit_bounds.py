#!/usr/bin/env python3
"""Outward-rounded enclosures along the true inverse orbit of U(s)=sF(s).
The seed is bracketed by two finite Stieltjes moment sums; no series convergence
is assumed. The recurrence uses only positive additions and multiplications.
Python Decimal elementary functions are enlarged by one adjacent representable
number on each side. The article supplies the proof of the exact identities.
"""
from __future__ import annotations
import csv, json
from decimal import Decimal as D, localcontext, ROUND_FLOOR, ROUND_CEILING, MAX_EMAX, MIN_EMIN
from fractions import Fraction as Q
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PREC=100

def directed(fn, up=False):
    with localcontext() as c:
        c.prec=PREC; c.rounding=ROUND_CEILING if up else ROUND_FLOOR
        c.Emax=MAX_EMAX; c.Emin=MIN_EMIN
        return +fn()

def elementary(x,method,up=False):
    with localcontext() as c:
        c.prec=PREC; c.Emax=MAX_EMAX; c.Emin=MIN_EMIN
        y=getattr(x,method)()
        return y.next_plus() if up else y.next_minus()

def main():
    with (ROOT/'data/coefficients.csv').open() as f:
        a=[int(row['A088714']) for row in csv.DictReader(f)]
    s=Q(1,100)
    sums=[]; value=Q(0)
    for n in range(32):
        value+=a[n]*(-s)**n
        sums.append(value)
    flo,fhi=sums[31],sums[30]
    assert 0<flo<fhi<1
    lo=directed(lambda:D((s*flo).numerator)/D((s*flo).denominator))
    hi=directed(lambda:D((s*fhi).numerator)/D((s*fhi).denominator),True)
    curlo=curhi=D('0.01')
    blo=directed(lambda:(elementary(D(5),'sqrt')-1)/2)
    bhi=directed(lambda:(elementary(D(5),'sqrt',True)-1)/2,True)
    records=[]
    for k in range(151):
        if k in (100,110,120,130,140,150) and lo>1:
            lprev=elementary(lo,'ln'); hprev=elementary(hi,'ln',True)
            lcur=elementary(curlo,'ln'); hcur=elementary(curhi,'ln',True)
            # A subtracted product needs the opposite rounding direction.
            product_hi=directed(lambda:bhi*hcur,True)
            product_lo=directed(lambda:blo*lcur)
            dlo=directed(lambda:lprev-product_hi)
            dhi=directed(lambda:hprev-product_lo,True)
            rlo=elementary(dlo,'exp'); rhi=elementary(dhi,'exp',True)
            records.append({'k':k,'log_s_lower':str(lcur),'log_s_upper':str(hcur),
                            'normalized_lower':str(rlo),'normalized_upper':str(rhi),
                            'note':'There is one true s_k in the displayed log interval; '
                                   's_k^alpha F(s_k) lies in the normalized interval.'})
        nxtlo=directed(lambda:curlo*(1+lo))
        nxthi=directed(lambda:curhi*(1+hi),True)
        lo,hi,curlo,curhi=curlo,curhi,nxtlo,nxthi
    report={'precision_decimal_digits':PREC,'seed_s':'1/100',
            'seed_F_lower':str(flo),'seed_F_upper':str(fhi),
            'seed_moment_orders':[31,30],'records':records}
    (ROOT/'data/orbit_bounds.json').write_text(json.dumps(report,indent=2)+'\n')
    for rec in records:
        print(rec['k'],D(rec['log_s_lower']),
              D(rec['normalized_lower']),D(rec['normalized_upper']))
if __name__=='__main__':main()
