#!/usr/bin/env python3
"""Rational root brackets using the positive squared-resolvent moments.

Seeds in data/root_brackets.json have no evidentiary status until the two
rational sign tests pass. This verifier requires no numerical library.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError('Run without -O: exact assertion checks are required.')
from fractions import Fraction as Q
from pathlib import Path
import json
from verify_global import mul, add, rat, dec_interval
from verify_identities import coeff
ROOT=Path(__file__).resolve().parents[1]

def sign_enclosure(a: int,b: int,m: Q,s: Q,N: int=36) -> tuple[Q,Q]:
    if type(a) is not int or type(b) is not int or type(N) is not int:
        raise TypeError('a, b, N must be integers')
    if N < 1:
        raise ValueError('N must be positive')
    if not (a>=8 and b>=1 and 0<=m<=Q(1,3) and 0<=s<=1):
        raise ValueError('Certificate domain violated')
    # E=1-(2/3)D, |E| <= 3/8 on this domain.
    e=[Q(1,3),Q(2,3)*s*m,-Q(2,3)*s]
    moments=[coeff(j+2,a,b)/Q(j+1) for j in range(2*N+1)]
    power=[Q(1)];out=Q(0)
    for k in range(N):
        p=mul([m,Q(-2)],power)
        out+=Q(4*(k+1),9)*sum((v*moments[j] for j,v in enumerate(p)),Q(0))
        power=mul(power,e)
    q=Q(3,8)
    error=Q(8,9)*Q(1,2**a)*q**N*(N+1-N*q)/(1-q)**2
    return out-error,out+error

def run() -> dict:
    seeds=json.loads((ROOT/'data'/'root_brackets.json').read_text())
    rows=[]
    for item in seeds['brackets']:
        a,b=item['a'],item['b'];s=Q(item['s']);lo=Q(item['m_lower']);hi=Q(item['m_upper'])
        assert 0<lo<hi<Q(1,3)
        L=sign_enclosure(a,b,lo,s);U=sign_enclosure(a,b,hi,s)
        assert L[1]<0<U[0],(a,b,s,L,U)
        rows.append({**item,'status':'PASS','P_at_lower_upper_bound':rat(L[1]),
                     'P_at_upper_lower_bound':rat(U[0]),
                     'eta_lower_decimal':dec_interval(lo/2,12)[0],
                     'eta_upper_decimal':dec_interval(hi/2,12)[1]})
    out={'status':'PASS','terms':36,'kernel_ratio_bound':'3/8','brackets':rows}
    (ROOT/'data'/'root_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
    return out
if __name__=='__main__':
    r=run();print('PASS:',len(r['brackets']),'exact angular-zero brackets')
    for t in r['brackets']:print(t['a'],t['b'],t['s'],t['eta_lower_decimal'],t['eta_upper_decimal'])
