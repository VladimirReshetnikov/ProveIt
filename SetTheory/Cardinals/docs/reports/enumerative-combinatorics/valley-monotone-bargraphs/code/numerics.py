#!/usr/bin/env python3
"""High-precision exploratory numerics; certificates are in verify.py."""
import json
from pathlib import Path
import mpmath as mp
from verify import exact_sequences
mp.mp.dps=60

def unimodal(q,j=2,J=400):
    u=mp.mpf(0)
    for k in range(J,j-1,-1):
        p=q**k;u=p/(1-p)+u/(1-p)**2
    return u

def bargraph(q,j=2,J=400):
    u=d=mp.mpf(0)
    for k in range(J,j-1,-1):
        p=q**k
        d=p/(1-p)+d/((1-p)*(1-p-p*u))
        u=p/(1-p)+u/(1-p)**2
    return d

def Q(q,j=1):return 1-q**j*(1+unimodal(q,j+1))
def K(q):return q/(1-q)*unimodal(q,2)

def main():
    r=mp.findroot(Q,(mp.mpf('.50'),mp.mpf('.51')))
    c=bargraph(r)/((1-r)*(-r*mp.diff(Q,r)))
    M=r*mp.diff(K,r)
    V=r*r*mp.diff(K,r,2)+M-M*M
    mu=1/M;var=V/M**3
    rows=[]
    for j in range(1,9):
        low=mp.mpf('.1');high=mp.mpf('.92')
        for _ in range(210):
            mid=(low+high)/2
            if Q(mid,j)>0:low=mid
            else:high=mid
        p=(low+high)/2
        cc=bargraph(p,j+1)/((1-p**j)*(-p*mp.diff(lambda z:Q(z,j),p)))
        for k in range(1,j):cc/=((1-p**k)*Q(p,k))
        rows.append({'j':j,'rho':str(p),'lambda':str(1/p),'C_real_sector':str(cc)})
    _,ds=exact_sequences(200);a=ds[1]
    errors=[]
    for n in (10,20,30,50,75,100,150,200):
        errors.append({'n':n,'d':a[n],
                       'ratio':str(mp.mpf(a[n])/a[n-1]),
                       'relative_error':str(mp.mpf(a[n])*r**n/c-1)})
    data={'rho':str(r),'lambda':str(1/r),'C':str(c),
          'mu':str(mu),'variance_coefficient':str(var),
          'unit_mean':str(M),'unit_variance':str(V),
          'mean_terminal_area':str(r*mp.diff(bargraph,r)/bargraph(r)),
          'positive_real_poles':rows,'error_table':errors,
          'warning':('Only rho, lambda and C bounds in verification.json are certified. '
                     'Working precision is not a truncation-error bound; final digits of '
                     'other fixed-cutoff values may be inaccurate.')}
    p=Path(__file__).with_name('numerical_results.json');p.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('positive_real_poles','error_table')},indent=2))
if __name__=='__main__':main()
