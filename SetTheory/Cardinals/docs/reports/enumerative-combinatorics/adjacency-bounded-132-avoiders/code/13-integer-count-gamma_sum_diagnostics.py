#!/usr/bin/env python3
"""Finite scalar-envelope diagnostics for the integer-count equivalent.
Floating-point values are not certified errors or asymptotic proof.
"""
from pathlib import Path
from math import log,exp,sqrt,pi,lgamma,floor
import json,platform
import numpy as np
import scipy
from scipy.optimize import brentq
from scipy.special import logsumexp
from fractions import Fraction
from math import factorial


def root_law(m):
    b=np.empty(m);b[0]=.25
    for k in range(1,m):b[k]=b[k-1]*(1-1.5/(k+1))
    k=np.arange(1,m+1,dtype=float)
    t=brentq(lambda t:np.dot(b,np.exp(t*k/m))-1,0,2*log(m)+10,xtol=1e-13)
    p=b*np.exp(t*k/m);res=float(p.sum()-1);p/=p.sum()
    return p,t,res


def coeffs(p,N):
    m=len(p);u=np.zeros(N+1);v=np.zeros(N+1);u[0]=v[0]=1
    for n in range(1,N+1):
        q=min(m,n)
        u[n]=np.dot(p[:q],u[n-q:n][::-1])
        v[n]=u[n]+np.dot(p[:q],v[n-q:n][::-1])
    return v


def gamma_terms(m,v):
    alpha=v/m;lo=floor(alpha)+1;hi=floor(alpha)+60
    result=[]
    for ell in range(lo,hi+1):
        s=ell-alpha
        if s<=0:continue
        z=log(ell+1)+1.5*s+(ell-1)*log(s)-ell*log(2*sqrt(pi*m))-lgamma(ell)
        result.append((ell,s,z))
    return result


def main():
    ratio_checks=0
    for ell in range(1,21):
        for a in range(1,11):
            s=Fraction(a,7)
            g=(ell+1)*s**(ell-1)/(2**ell*factorial(ell-1))
            gp=(ell+2)*(s+1)**ell/(2**(ell+1)*factorial(ell))
            expected=Fraction(ell+2,ell+1)*s/Fraction(2*ell)*(1+1/s)**ell
            assert gp/g==expected;ratio_checks+=1
    rows=[]
    for m in (64,128,256,512,1024,2048):
        targets=[round(m*(floor(c*log(m))+f)) for c in (.25,.5,1) for f in (0,.5)]
        targets=[v for v in targets if v>=m]
        p,t,res=root_law(m);vs=coeffs(p,max(targets))
        for v in targets:
            terms=gamma_terms(m,v);lg=logsumexp([r[2] for r in terms])
            # E_m(v+1)/4^(v+1) = exp(-t*v/m)*V(v)/4.
            log_exact=log(vs[v])-t*v/m-log(4)
            log_predicted=lg-log(m)
            ordered=sorted(terms,key=lambda r:r[2],reverse=True)
            rows.append(dict(m=m,n=v+1,c=v/(m*log(m)),phase=(v/m)%1,
                             scalar_envelope_to_gamma_sum=exp(log_exact-log_predicted),
                             first_count=ordered[0][0],first_deficit=ordered[0][1],
                             second_count=ordered[1][0],second_to_first=exp(ordered[1][2]-ordered[0][2]),
                             root_residual=res))
    data=dict(status='finite checks completed',exact_adjacent_ratio_checks=ratio_checks,
              scope='The exact rational checks concern the summand-ratio identity. Floating-point envelope ratios are illustrative, with no asserted finite error bound.',
              environment=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__),
              rows=rows)
    Path(__file__).with_name('gamma_sum_diagnostics.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(exact_adjacent_ratio_checks=ratio_checks,envelope_rows=len(rows),status=data['status'])))

if __name__=='__main__':main()
