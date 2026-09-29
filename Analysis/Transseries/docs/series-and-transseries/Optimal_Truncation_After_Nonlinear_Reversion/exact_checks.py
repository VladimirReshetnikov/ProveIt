#!/usr/bin/env python3
"""Exact-rational formal audits and shifted digamma inverse certificates.

Only Python's standard library is used.  This is executable rational arithmetic,
not a proof-assistant verification of the analytic lemmas in the article.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
import sys
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def bernoulli(nmax: int) -> list[Q]:
    b = [Q(1)]
    for n in range(1, nmax+1):
        b.append(-sum((Q(comb(n+1,k))*b[k] for k in range(n)), Q(0))/(n+1))
    return b


def forward_coeffs(nmax: int) -> list[Q]:
    b = bernoulli(2*nmax)
    return [Q(0)]+[-(Q(1,2**(2*j-1))-1)*b[2*j]/(2*j)
                    for j in range(1,nmax+1)]


def inverse_coeffs(c: list[Q], nmax: int) -> list[Q]:
    h = [Q(1)]
    for n in range(1,nmax+1):
        s = 2*n-1
        a = [Q(1)]
        for k in range(1,n+1):
            a.append(s*sum((j*c[j]*a[k-j] for j in range(1,k+1)),Q(0))/k)
        h.append(-a[n]/s)
    return h


def mul(a: list[Q], b: list[Q], n: int) -> list[Q]:
    return [sum((a[j]*b[k-j] for j in range(k+1)),Q(0)) for k in range(n+1)]


def inv(a: list[Q], n: int) -> list[Q]:
    b = [1/a[0]]
    for k in range(1,n+1):
        b.append(-sum((a[j]*b[k-j] for j in range(1,k+1)),Q(0))/a[0])
    return b


def exact_formal_audit(n: int = 12) -> None:
    c=forward_coeffs(n); h=inverse_coeffs(c,n)
    qi=inv(h,n)
    # log(q)'=q'/q, integrated coefficientwise.
    logq=[Q(0)]+[sum((j*h[j]*qi[k-j] for j in range(1,k+1)),Q(0))/k
                   for k in range(1,n+1)]
    qiminus2=mul(qi,qi,n)
    arg=[Q(0)]+qiminus2[:n]
    power=[Q(1)]+[Q(0)]*n
    res=logq[:]
    for j in range(1,n+1):
        power=mul(power,arg,n)
        res=[res[k]+c[j]*power[k] for k in range(n+1)]
    assert all(x==0 for x in res)
    assert h[1:5]==[Q(-1,24),Q(3,640),Q(-1525,580608),Q(615881,199065600)]
    print(f'Exact formal inverse residual: all {n+1} coefficients vanish.')


def log_enclosure(r: Q, n: int) -> tuple[Q,Q]:
    if r <= 0 or n < 1:
        raise ValueError('r must be positive and n must be positive')
    t=(r-1)/(r+1)
    s=2*sum((t**(2*k+1)/(2*k+1) for k in range(n)),Q(0))
    tail=2*abs(t)**(2*n+1)/((2*n+1)*(1-t*t))
    return s-tail,s+tail


def residual_enclosure(v: Q,x: Q,shift: int,k: int,nlog: int,c:list[Q]) -> tuple[Q,Q]:
    w=v+shift
    lo,hi=log_enclosure(w/x,nlog)
    rational=sum((c[j]/w**(2*j) for j in range(1,k+1)),Q(0))
    rational-=sum((1/(v+Q(1,2)+j) for j in range(shift)),Q(0))
    rem=abs(c[k+1])/w**(2*k+2)
    if k%2==0:
        return lo+rational,hi+rational+rem
    return lo+rational-rem,hi+rational


def decimal_outward(q: Q, digits: int, upper: bool) -> str:
    unit=10**digits
    scaled=q.numerator*unit
    n=-((-scaled)//q.denominator) if upper else scaled//q.denominator
    sign='-' if n<0 else ''
    n=abs(n)
    return f'{sign}{n//unit}.{n%unit:0{digits}d}'


def certificate(xint:int,m:int,kind:str,c:list[Q],h:list[Q]) -> dict[str,object]:
    x=Q(xint); a=x-1/(12*x)
    v=x+sum((h[j]*x**(1-2*j) for j in range(1,m+1)),Q(0))
    if kind=='midpoint':
        v+=h[m+1]*x**(-2*m-1)/2
    assert a<v<x
    shift=xint
    k=6*xint
    nlog=20*xint
    rlo,rhi=residual_enclosure(v,x,shift,k,nlog,c)
    lower_slope=1/(x+Q(1,2))
    upper_slope=1/(a+Q(1,2))+1/(a+Q(1,2))**2
    assert rlo*rhi>0, 'Increase shift, forward order, or log order.'
    if rlo>0:
        dlo,dhi=rlo/upper_slope,rhi/lower_slope
    else:
        dlo,dhi=rlo/lower_slope,rhi/upper_slope
    digits=6*xint+20
    out={'X':xint,'M':m,'approximation':kind,'shift':shift,
         'forward_order':k,'log_terms':nlog,
         'error_lower_outward_decimal':decimal_outward(dlo,digits,False),
         'error_upper_outward_decimal':decimal_outward(dhi,digits,True),
         'error_sign':1 if dlo>0 else -1,
         'candidate_numerator':str(v.numerator),'candidate_denominator':str(v.denominator),
         'exact_error_lower':[str(dlo.numerator),str(dlo.denominator)],
         'exact_error_upper':[str(dhi.numerator),str(dhi.denominator)]}
    print(xint,m,kind,'error in [',out['error_lower_outward_decimal'],',',
          out['error_upper_outward_decimal'],']')
    return out


def main() -> None:
    exact_formal_audit()
    c=forward_coeffs(49);h=inverse_coeffs(c,26)
    certs=[]
    for x,m in [(3,9),(5,15),(8,25)]:
        for kind in ['direct','midpoint']:
            certs.append(certificate(x,m,kind,c,h))
    path=Path(__file__).with_name('exact_certificates.json')
    path.write_text(json.dumps(certs,indent=2)+'\n')
    print('All six exact sign/enclosure checks passed. Wrote',path.name)

if __name__=='__main__':
    main()
