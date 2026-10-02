#!/usr/bin/env python3
"""Independent exact recurrence, precision comparison, Jensen and inverse checks."""
import csv
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp
from verify import OUT, coefficients, saddle, saddle_sums


def divisor_recurrence(nmax: int, s: int) -> list[int]:
    b=[0]*(nmax+1)
    for k in range(1,nmax+1):
        for m in range(k,nmax+1,k):
            j=m//k
            b[m]+=(-1)**(j+1)*k**(s*j+1)
    a=[1]+[0]*nmax
    for n in range(1,nmax+1):
        v=sum(b[m]*a[n-m] for m in range(1,n+1))
        assert v % n == 0
        a[n]=v//n
    return a


def gaussian_inverse(log_target: mp.mpf, s: int=1,
                     t_guess: mp.mpf | None=None) -> mp.mpf:
    """Invert the Gaussian log-saddle approximant; return a real index.

The article proves asymptotic <=1+o(1) error for integer threshold inversion.
No finite-input rounding guarantee or interval certification is claimed.
"""
    y=mp.mpf(log_target)
    if y<=1 or s<=0:
        raise ValueError('use log_target > 1 and s > 0')
    if t_guess is None:
        w=mp.lambertw(y/(s*mp.e)).real
        N=y/(s*w)
        t_guess=s*mp.log(N)/N
    t=mp.mpf(t_guess)
    for _ in range(20):
        phi,k,_=saddle_sums(t,s,3)
        psi=phi+t*k[1]-mp.log(2*mp.pi*k[2])/2
        der=-t*k[2]+k[3]/(2*k[2])
        if der>=0:
            raise ArithmeticError('not in the eventually increasing index regime')
        step=(psi-y)/der
        nt=t-step
        if nt<=0: nt=t/2
        if abs(nt-t)<mp.power(10,-mp.mp.dps+12):
            t=nt;break
        t=nt
    else:
        raise ArithmeticError('inverse failed to converge')
    return saddle_sums(t,s,1)[1][1]


def main():
    record={}
    for s in [1,2,3]:
        a=[int(v) for v in json.loads((OUT/f'exact_s{s}.json').read_text())]
        assert divisor_recurrence(200,s)==a[:201]
    record['independent_recurrence']='exact match through n=200 for s=1,2,3'
    # Exact real-root count, not floating root finding.
    X=sp.symbols('X')
    a=[int(v) for v in json.loads((OUT/'exact_s1.json').read_text())]
    jensen=[]
    for n in [100,1000,5000]:
        for d in [2,3,4,5]:
            p=sp.Poly(sum(math.comb(d,j)*a[n+j]*X**j for j in range(d+1)),X)
            real=int(p.count_roots(-sp.oo,sp.oo))
            squarefree=sp.gcd(p,p.diff()).degree()==0
            jensen.append({'n':n,'d':d,'real_roots':real,'squarefree':squarefree})
    record['jensen_exact']=jensen
    r40=list(csv.DictReader((OUT/'saddle_s1_dps40.csv').open()))[-1]
    r60=list(csv.DictReader((OUT/'saddle_s1_dps60.csv').open()))[-1]
    mp.mp.dps=60
    errs=[abs(mp.mpf(r40[f'relative_error_J{j}'])-mp.mpf(r60[f'relative_error_J{j}'])) for j in range(4)]
    record['precision_40_60_max_difference']=mp.nstr(max(errs),12)
    # Invert at an exact coefficient, using a fully converged inverse, not
    # merely the first Newton correction displayed in the other CSV files.
    mp.mp.dps=45
    n=10000
    t,_,_,_=saddle(n,1,2)
    x0=gaussian_inverse(mp.log(a[n]),1,t)
    L=-mp.lambertw(-t,-1).real
    record['gaussian_inverse_at_a10000']={'x0':mp.nstr(x0,40),
        'x0_minus_n':mp.nstr(x0-n,30),
        'scaled_displacement':mp.nstr((x0-n)*(-8*L**2/3),30)}
    dest=OUT/'extra_checks.json';dest.write_text(json.dumps(record,indent=2))
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
