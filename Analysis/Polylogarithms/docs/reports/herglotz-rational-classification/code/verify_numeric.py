#!/usr/bin/env python3
"""High-precision diagnostic checks, not interval certificates.

The defining integral is evaluated after t=u^q, so all exponents in the
integrand are integers. Right-hand sides use independent log-sine sums or
classical dilogarithms. The proofs are in article.tex.
"""
from __future__ import annotations
import argparse
import json
import platform
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]


def integral(p:int,q:int):
    r=Fraction(p,q);p,q=r.numerator,r.denominator
    return mp.quad(lambda u:q*u**(q-1)*mp.log1p(u**p)/(1+u**q),[0,mp.mpf('0.5'),1])


def S(n:int):
    return mp.fsum(mp.log(2*mp.sin(mp.pi*k/n))**2 for k in range(1,n))


def neighbor(n:int):
    return (mp.log(2)**2/2+(S(n)-S(n+1)+S(2*n+2)-S(2*n))/2
            -mp.pi**2*(n*n-n-1)/(24*n*(n+1)))


def j35():
    phi=(1+mp.sqrt(5))/2
    return (mp.polylog(2,mp.mpf(1)/3)-mp.polylog(2,mp.mpf(1)/5)/2
            +mp.log(2)**2/2+mp.log(3)**2/2-mp.log(5)**2/4
            +mp.log(phi)**2-7*mp.pi**2/180)


def run(dps:int):
    mp.mp.dps=dps
    rows=[]
    def record(name,lhs,rhs):
        residual=abs(lhs-rhs)
        assert residual < mp.mpf(10)**(-dps+15), (name,residual)
        rows.append({'name':name,'lhs':mp.nstr(lhs,dps-10),
                     'absolute_residual':mp.nstr(residual,12)})
    for n in list(range(1,21))+[30,50,100]:
        record(f'neighbor_{n}',integral(n,n+1),neighbor(n))
    phi=(1+mp.sqrt(5))/2;a=mp.log(2);d=mp.log(phi);u=mp.log(1+mp.sqrt(2))
    record('J_1_3',integral(1,3),mp.pi**2/9+a*a/2-mp.log(3)**2/2-mp.polylog(2,mp.mpf(1)/3))
    record('J_1_5',integral(1,5),7*mp.pi**2/60+a*a/2-mp.log(5)**2/4-d*d-mp.polylog(2,mp.mpf(1)/5)/2)
    record('J_3_5',integral(3,5),j35())
    record('exceptional_linear_identity',integral(1,3)-integral(1,5)+integral(3,5),a*a/2+2*d*d-2*mp.pi**2/45)
    record('J_5_3',integral(5,3),a*a-j35())
    record('J_4_3',integral(4,3),7*a*a/8-u*u/2+5*mp.pi**2/288)
    record('J_4_5',integral(4,5),7*a*a/8+2*d*d-u*u/2-11*mp.pi**2/480)
    for p,q in [(1,2),(2,3),(3,5),(4,15),(5,12),(8,3),(7,1),(17,23)]:
        record(f'reciprocity_{p}_{q}',integral(p,q)+integral(q,p),a*a)
    # A numerical sanity check of the exact positivity witness in the audit.
    A,B,C=[mp.log(2*mp.sin(mp.pi*k/7)) for k in (1,2,3)]
    det=-(B-A)**2-(C-B)*(C-A)
    assert det < 0
    return {'dps':dps,'status':'PASS','number_of_checks':len(rows),
            'checks':rows,'audit_log_determinant':mp.nstr(det,dps-10)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',nargs='+',type=int,default=[90,140])
    args=parser.parse_args()
    if min(args.dps)<40:
        parser.error('use at least 40 decimal digits')
    result={'status':'PASS','python':platform.python_version(),'mpmath':mp.__version__,
            'scope':'arbitrary-precision diagnostics; NOT rigorous error enclosures',
            'runs':[run(dps) for dps in args.dps]}
    (ROOT/'data'/'numeric_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='runs'},indent=2))
    print('Runs:',[(r['dps'],r['number_of_checks']) for r in result['runs']])

if __name__=='__main__':
    main()
