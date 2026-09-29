#!/usr/bin/env python3
"""Exact rational certificates for the positive inverse harmonic function.

mpmath proposes an approximation; every enclosure assertion uses Fraction only.
The finite log series has an explicit rational tail bound. The mathematical
certificate is proved in the accompanying article, not delegated to mpmath.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import json
import mpmath as mp
from verify import coeffs_c, mpr


def log_interval(r: Q, tolerance: Q) -> tuple[Q,Q,int]:
    if r <= 0 or tolerance <= 0:
        raise ValueError('positive logarithm argument and tolerance required')
    t=(r-1)/(r+1); t2=t*t
    term=t; total=Q(0); k=0
    while True:
        total += 2*term/(2*k+1)
        k += 1; term *= t2
        tail = 2*abs(term)/((2*k+1)*(1-t2))
        if tail <= tolerance:
            return total-tail,total+tail,k
        if k > 10000:
            raise ArithmeticError('log series did not reach requested tolerance')


def forward_polynomial(c: list[Q], M: int, v: Q) -> Q:
    z=1/(v*v); acc=Q(0)
    for j in range(M,0,-1):
        acc=(acc+c[j])*z
    return acc


def certify(X: Q, v: Q, M: int, c: list[Q]) -> tuple[Q,Q,int]:
    if X < 1 or M < 0 or len(c) <= M+1:
        raise ValueError('X>=1, M>=0, and enough coefficients required')
    a=X-1/(12*X)
    if not a <= v <= X:
        raise ValueError('candidate must be inside the proved initial bracket')
    E=abs(c[M+1])/v**(2*M+2)
    lo,hi,steps=log_interval(v/X,E/1000)
    corr=forward_polynomial(c,M,v)
    residual=max(abs(lo+corr),abs(hi+corr))
    radius=(X+Q(1,2))*(residual+E)
    return v-radius,v+radius,steps


def forward_residual_interval(X: Q, v: Q, M: int, c: list[Q]) -> tuple[Q,Q]:
    E=abs(c[M+1])/v**(2*M+2)
    lo,hi,_=log_interval(v/X,E/10**6)
    corr=forward_polynomial(c,M,v)
    # F(v)-P_M(v) has sign (-1)^M and magnitude < E.
    return lo+corr-(E if M%2 else 0), hi+corr+(0 if M%2 else E)


def outward_decimal(a: Q, b: Q, places: int) -> tuple[str,str]:
    scale=10**places
    low=(a.numerator*scale)//a.denominator
    high=-((-b.numerator*scale)//b.denominator)
    def fmt(n: int) -> str:
        sign='-' if n<0 else ''; s=str(abs(n)).zfill(places+1)
        return sign+s[:-places]+'.'+s[-places:]
    return fmt(low),fmt(high)


def main() -> None:
    mp.mp.dps=200
    c=coeffs_c(128); out=[]
    for xx in [5,10,20,40]:
        X=Q(xx); xm=mp.mpf(xx); M=int(mp.floor(mp.pi*xm))
        initial_a=X-1/(12*X)
        initial_E=abs(c[M+1])/initial_a**(2*M+2)
        d=1/(12*X*X)-1/(24*initial_a*initial_a)
        ell=1/(24*X*X)-Q(7,960)/X**4
        assert initial_E < min(d,ell)
        assert (2*M+2)*initial_E/initial_a < 1/(X+Q(1,2))
        cm=[mpr(x) for x in c[:M+1]]
        u=mp.findroot(lambda v:mp.log(v/xm)+mp.fsum(cm[j]/v**(2*j)
                     for j in range(1,M+1)),(xm-1/(12*xm),xm))
        # Proposal only: its accuracy is neither assumed nor needed by certify().
        v=Q(mp.nstr(u,180))
        a,b,steps=certify(X,v,M,c)
        places=int(mp.ceil(2*mp.pi*xm/mp.log(10)))+8
        lo,hi=outward_decimal(a-Q(1,2),b-Q(1,2),places)
        assert Q(lo) <= a-Q(1,2) <= b-Q(1,2) <= Q(hi)
        assert forward_residual_interval(X,Q(lo)+Q(1,2),M,c)[1] < 0
        assert forward_residual_interval(X,Q(hi)+Q(1,2),M,c)[0] > 0
        out.append({'X':xx,'M':M,'target':'H(x) = gamma + log(X)',
                    'lower_x':lo,'upper_x':hi,'log_terms':steps,
                    'outward_decimal_places':places,
                    'exact_endpoint_sign_checks_passed':True,
                    'exact_truncation_root_conditions_passed':True,
                    'certificate_arithmetic':'exact fractions and analytic remainder inequality'})
    dest=Path(__file__).resolve().parent/'certificates.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
