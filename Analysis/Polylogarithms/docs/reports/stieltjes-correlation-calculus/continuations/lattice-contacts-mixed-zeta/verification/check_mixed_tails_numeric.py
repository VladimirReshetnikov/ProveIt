#!/usr/bin/env python3
"""Numerical diagnostics for ordinary mixed-tail sums; requires mpmath.
Finite tail cutoffs are completed by a fixed centered asymptotic expansion.
These are numerical diagnostics, not interval certificates.
"""
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
from pathlib import Path
import json
import mpmath as mp
from verify_mixed_tails import halfbern

mp.mp.dps=90

def fmp(q):return mp.mpf(q.numerator)/q.denominator

@lru_cache(None)
def eta(p,j):
    return F(1,p-1) if j==0 else F(factorial(p+2*j-2),factorial(p-1)*factorial(2*j))*halfbern(2*j)

@lru_cache(None)
def centered(P,j):
    if not P:return F(j==0)
    return sum((eta(P[0],r)*centered(P[1:],j-r) for r in range(j+1)),F())

def ordinary_moment(P,m,N,J):
    w=sum(P)-len(P);cut=(m-w)//2
    out=mp.mpf(0)
    for n in range(N):
        x=mp.mpf(n)+mp.mpf('0.5')
        v=x**m*mp.fprod(mp.zeta(p,n+1) for p in P)
        for j in range(cut+1):v-=fmp(centered(P,j))*x**(m-w-2*j)
        out+=v
    for j in range(max(0,cut+1),J):
        out+=fmp(centered(P,j))*mp.zeta(w+2*j-m,mp.mpf(N)+mp.mpf('0.5'))
    return out

def main():
    z=lambda k:mp.zeta(k)
    E=mp.mpf(15)/2*z(5)-3*z(2)*z(3)
    rhs={
       1:E-mp.mpf(5)/16*z(6),
       3:z(2)/12+z(3)-mp.mpf(7)/16*z(4)-E/6+mp.mpf(5)/64*z(6),
       5:-mp.mpf(19)/360-mp.mpf(29)/360*z(2)-mp.mpf(7)/12*z(3)+mp.mpf(35)/96*z(4)+mp.mpf(47)/720*E-mp.mpf(35)/768*z(6),
       7:mp.mpf(761)/20160+mp.mpf(2257)/20160*z(2)+mp.mpf(61)/120*z(3)-mp.mpf(343)/768*z(4)-mp.mpf(257)/5040*E+mp.mpf(155)/3072*z(6)
    }
    out={'precision_digits':mp.mp.dps,'status':'numerical diagnostics only','triple':[]}
    for N,J in [(40,35),(64,48)]:
        for m,v in rhs.items():
            lhs=ordinary_moment((2,2,4),m,N,J);err=abs(lhs-v)
            out['triple'].append({'moment':m,'cutoff':N,'asymptotic_terms':J,'value':mp.nstr(lhs,65),'absolute_error':mp.nstr(err,8)})
            print('triple',m,'N',N,'J',J,'error',mp.nstr(err,8))
            assert err<mp.mpf('1e-48')
    coeffs=[2526903,80590275,474388272,753887520,353617920,42197760]
    lhs=sum(c*ordinary_moment((2,2,4),2*j+1,64,48) for j,c in enumerate(coeffs))
    out['rational_identity']={'value':mp.nstr(lhs,70),'absolute_error':mp.nstr(abs(lhs+6199420),8)}
    print('rational sum error',out['rational_identity']['absolute_error'])
    assert abs(lhs+6199420)<mp.mpf('1e-45')
    # The quartic m=0 anchor is evaluated by its direct convergent tail sum;
    # the m=2 relation then has an independent elementary right side.
    A9=ordinary_moment((2,2,2,4),0,64,48)
    B7=mp.mpf(59)/24*z(3)*z(4)+mp.mpf(23)/12*z(2)*z(5)-mp.mpf(203)/32*z(7)
    v=2*B7+rhs[1]-A9/12
    lhs=ordinary_moment((2,2,2,4),2,40,35)
    out['quartic_m2']={'anchor_A9':mp.nstr(A9,65),'constant_B7':mp.nstr(B7,65),'value':mp.nstr(lhs,65),'absolute_error':mp.nstr(abs(lhs-v),8)}
    print('quartic m2 error',out['quartic_m2']['absolute_error'])
    assert abs(lhs-v)<mp.mpf('1e-48')
    Path(__file__).resolve().parents[1]/'results'/'mixed_tail_numeric.json'.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
