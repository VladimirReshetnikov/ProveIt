#!/usr/bin/env python3
"""Locate the unique n=2, k=1 lower-branch minimum using exact rationals.

The analytic uniqueness theorem is in article.tex. This program proves that
its rho-coordinate lies in (0.91560506, 0.91560508); it does not relabel an
unvalidated numerical solve as an interval proof.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
from math import factorial
from certify import I, outward, logq, horner, polynomial, pack, fracstr

def fi(n,k,a:I):
    loga=I(logq(a.lo).lo,logq(a.hi).hi)
    return outward(factorial(k)*horner(polynomial(n,k),-loga)/(a**(k+1)))

def tail(n,k,r,a_upper:Q,rho:Q,M:int):
    if not 0<rho<1 or r not in (0,1,2) or k<1:raise ValueError('Invalid inputs')
    # log(x)^q <= q! x for x>=1, and m^(falling r) <= (a+m)^r.
    K=factorial(k)*sum(c*factorial(q) for q,c in enumerate(polynomial(n,k)))
    if r<=k:
        return K*rho**(M-r)/(1-rho)
    return K*rho**(M-r)*((a_upper+M)/(1-rho)+rho/(1-rho)**2)

def deformed(n,k,a:I,rho:Q,r:int=0,M:int=500):
    if a.lo<=0 or a.lo+M<1:raise ValueError('Invalid a or tail start')
    v=I.point(0);pw=I.point(1)
    for m in range(M):
        falling=1
        for j in range(r):falling*=m-j
        if falling:
            v=outward(v+pw*Q(falling,rho**r)*fi(n,k,a+m))
        pw=outward(pw*rho)
    R=tail(n,k,r,a.hi,rho,M)
    return outward(v+I(-R,R))

def main():
    alo=Q('0.878632683855767');ahi=Q('0.878632683855769')
    rows=[]
    for text,sign in [('0.91560506',-1),('0.91560508',1)]:
        rho=Q(text)
        fl=deformed(2,1,I.point(alo),rho)
        fu=deformed(2,1,I.point(ahi),rho)
        fr=deformed(2,1,I(alo,ahi),rho,1)
        assert fl.sign==1 and fu.sign==-1 and fr.sign==sign
        rows.append({'rho':fracstr(rho),'a_bracket':[fracstr(alo),fracstr(ahi)],
                     'F_at_lower_a':pack(fl),'F_at_upper_a':pack(fu),
                     'F_rho_on_a_bracket':pack(fr),'M':500})
        print(text, 'root bracket certified; sign(F_rho)=',fr.sign)
    result={'minimum_rho_open_interval':['0.91560506','0.91560508'],
            'arithmetic':'exact rational with rigorous geometric tail',
            'depends_on':'analytic uniqueness and saturation theorems in article.tex',
            'certificates':rows}
    out=Path(__file__).resolve().parent.parent/'data'/'minimum_location_certificate.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: unique minimum rho is in (0.91560506, 0.91560508).')
if __name__=='__main__':main()
