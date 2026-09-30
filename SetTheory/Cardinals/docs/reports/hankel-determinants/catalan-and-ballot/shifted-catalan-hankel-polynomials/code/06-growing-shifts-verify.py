#!/usr/bin/env python3
"""Reproduce the finite audits in A Catalan Law Behind Growing Shifts.

Exact assertions use fractions.Fraction and do not rely on floating-point roots.
Numerical tables are diagnostics, not interval certificates or universal proofs.
Run: python code/verify.py --output data
Dependencies: Python >=3.10, numpy, scipy; no network access required.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from fractions import Fraction as F
from pathlib import Path
import warnings
import numpy as np
import scipy
from scipy.special import logsumexp, roots_jacobi
from scipy.stats import norm, poisson

def parameters(n: int, m: int):
    if n < 1 or m < 0:
        raise ValueError('Require n >= 1 and m >= 0.')
    v = F(2*m+1, 2)
    B = n+m+1
    c = v/(n*B)
    beta = (1+c*(v+F(3,2)))/(v+1)
    theta = 1/((v+1)*beta)
    mu = n*B/(4*v)
    return v, B, c, beta, theta, mu

def coefficients(n: int, m: int) -> list[F]:
    v, B, *_ = parameters(n, m)
    a = [F(1)]
    for k in range(n):
        a.append(a[-1]*F(n-k,n)*F(B+k,B)*v/(v+k)/F(k+1))
    return a

def moments_from_coefficients(a: list[F], order: int) -> list[F]:
    l: list[F] = []
    for k in range(order):
        b = (k+1)*a[k+1] if k+1<len(a) else F(0)
        l.append(b-sum(a[j]*l[k-j] for j in range(1,min(k,len(a)-1)+1)))
    return [F(0)]+[(-1)**k*l[k] for k in range(order)]

def moments(n: int, m: int, order: int) -> list[F]:
    v, B, c, *_ = parameters(n,m)
    p = [F(0),F(1)]
    for k in range(1,order):
        cv = sum(p[i]*p[k+1-i] for i in range(1,k+1))
        pv = sum(p[i]*p[k-i] for i in range(1,k))
        p.append((cv+c*(k+v+F(1,2))*p[k]-c*pv)/(v+k))
    return p

def catalan(k: int) -> int:
    return math.comb(2*k,k)//(k+1)

def determinant(matrix: list[list[F]]) -> F:
    a = [row[:] for row in matrix]
    n = len(a)
    ans = F(1)
    for i in range(n):
        pivot = next((j for j in range(i,n) if a[j][i]),None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i],a[pivot] = a[pivot],a[i]
            ans = -ans
        p = a[i][i]
        ans *= p
        for j in range(i+1,n):
            q = a[j][i]/p
            for k in range(i+1,n):
                a[j][k] -= q*a[i][k]
    return ans

def pure_hankel(n: int, m: int) -> F:
    result=F(1)
    for i in range(1,m):
        for j in range(1,i+1):
            result *= F(2*n+i+j,i+j)
    return result

def exact_audit() -> dict[str,int]:
    counts={'direct_determinants':0,'moment_parameter_pairs':0,
            'individual_moment_equalities':0,'moment_majorants':0,
            'limiting_recurrence_cases':0}
    for n in range(1,7):
        for m in range(9):
            coeff=coefficients(n,m)
            *_,mu=parameters(n,m)
            for a in [F(-2),F(-1,3),F(0),F(1,3),F(2)]:
                direct=determinant([[a*catalan(i+j+m)+catalan(i+j+m+1)
                                     for j in range(n)] for i in range(n)])
                tau=mu*a
                val=sum(ck*tau**k for k,ck in enumerate(coeff))
                assert direct==pure_hankel(n,m+1)*val,(n,m,a)
                counts['direct_determinants']+=1
    for n in range(1,21):
        for m in range(21):
            p=moments(n,m,12)
            q=moments_from_coefficients(coefficients(n,m),12)
            assert p==q,(n,m)
            counts['moment_parameter_pairs']+=1
            counts['individual_moment_equalities']+=12
            v,B,c,beta,theta,mu=parameters(n,m)
            assert p[2]==beta and beta>=F(1,n) and beta>=1/(v+1)
            for k in range(1,13):
                assert 0<p[k]<=catalan(k-1)*(2*beta)**(k-1)
                counts['moment_majorants']+=1
    for theta in [F(0),F(1,7),F(1,2),F(2,3),F(1)]:
        gamma=1-theta
        d=[F(0),F(1)]
        for k in range(1,13):
            d.append(theta*sum(d[i]*d[k+1-i] for i in range(1,k+1))
                     +gamma*d[k]
                     -theta*gamma*sum(d[i]*d[k-i] for i in range(1,k)))
            closed=sum(F(math.comb(k,j)*catalan(j))*theta**j*gamma**(k-j)
                       for j in range(k+1))
            assert d[k+1]==closed
            counts['limiting_recurrence_cases']+=1
    return counts

def distribution(n: int,m: int,tau: float):
    if tau <=0:
        if tau<0: raise ValueError('tau must be nonnegative')
        p=np.zeros(n+1);p[0]=1
        return 0.,p
    v=float(F(2*m+1,2));B=n+m+1.
    k=np.arange(n,dtype=float)
    logr=(math.log(tau)-np.log(k+1)+np.log1p(-k/n)
          +np.log1p(k/B)-np.log1p(k/v))
    logs=np.r_[0.,np.cumsum(logr)]
    logR=float(logsumexp(logs))
    return logR,np.exp(logs-logR)

def limiting_moment(k:int,theta:float)->float:
    return sum(math.comb(k-1,j)*catalan(j)*theta**j*(1-theta)**(k-1-j)
               for j in range(k))

def free_energy(theta:float,t:float)->float:
    from scipy.integrate import quad
    if t<0: raise ValueError('t must be nonnegative')
    def slope(s):
        g=1-theta
        return 2/((1+g*s)*(1+math.sqrt(1+4*theta*s/(1+g*s))))
    return quad(slope,0.,t,epsabs=1e-12,epsrel=1e-12)[0]

def saddle(n:int,m:int,t:float):
    r=(m+.5)/n;b=(n+m+1)/n
    aa=r*t+b;bb=b*r-r*t*(1-b);cc=r*t*b
    q=2*cc/(bb+math.sqrt(bb*bb+4*aa*cc))
    f=(q*math.log(t/q)-(1-q)*math.log1p(-q)
       +(b+q)*math.log1p(q/b)-(r+q)*math.log1p(q/r))
    h=1/q+1/(1-q)+1/(r+q)-1/(b+q)
    A=math.sqrt(b*(r+q)/(q*(1-q)*r*(b+q)*h))
    return q,f,A,1/h

def write_csv(path:Path, rows:list[dict]):
    with path.open('w',newline='') as f:
        out=csv.DictWriter(f,fieldnames=list(rows[0]))
        out.writeheader();out.writerows(rows)

def numerical_audit(output:Path):
    rows=[]
    for n in [64,256,1024,4096,16384]:
        m=n;_,_,_,beta,theta,_=parameters(n,m);beta=float(beta)
        tau=1/math.sqrt(beta)
        logR,_=distribution(n,m,tau)
        tauP=beta**(-2/3)
        _,p=distribution(n,m,tauP)
        k=np.arange(n+1)
        tv=.5*(np.abs(p-poisson.pmf(k,tauP)).sum()+poisson.sf(n,tauP))
        mean=float(np.dot(k,p));var=float(np.dot((k-mean)**2,p))
        rows.append(dict(n=n,m=m,beta=beta,det_ratio=math.exp(logR-tau),
                         det_limit=math.exp(-.5),tau_poisson=tauP,
                         tv=float(tv),tv_limit=2*norm.cdf(.5)-1,
                         mean_shift=(mean-tauP)/math.sqrt(tauP),
                         variance_ratio=var/tauP))
    write_csv(output/'critical_scales.csv',rows)
    spectral=[]
    for n,m in [(64,4096),(128,128),(4096,64),(512,512),(2048,2048)]:
        _,_,_,beta,theta,_=parameters(n,m)
        p=moments(n,m,6)
        for k in range(2,7):
            observed=float(p[k]/beta**(k-1))
            expected=limiting_moment(k,float(theta))
            spectral.append(dict(n=n,m=m,k=k,theta=float(theta),
                                 moment=observed,limit_profile=expected,
                                 difference=observed-expected))
    write_csv(output/'spectral_moments.csv',spectral)
    frees=[]
    for n,m in [(256,65536),(1024,1024),(65536,256),(4096,4096)]:
        *_,beta,theta,mu=parameters(n,m)
        beta=float(beta);theta=float(theta)
        for t in [.25,1.,4.]:
            logR,_=distribution(n,m,t/beta)
            Ftheta=free_energy(theta,t)
            frees.append(dict(n=n,m=m,t=t,theta=theta,
                              scaled_logR=beta*logR,free_energy=Ftheta,
                              difference=beta*logR-Ftheta))
    write_csv(output/'free_energy.csv',frees)
    saddles=[]
    for n in [32,128,512,2048]:
        for ratio in [.25,1.,4.]:
            m=int(n*ratio)
            for t in [.2,1.,3.]:
                logR,p=distribution(n,m,n*t)
                q,f,A,V=saddle(n,m,t)
                rel=math.expm1(logR-n*f-math.log(A))
                saddles.append(dict(n=n,m=m,t=t,q=q,
                                    relative_error=rel,n_times_error=n*rel))
    write_csv(output/'saddle_prefactor.csv',saddles)
    root_checks=0
    for n in [8,16,32,64]:
        for m in [0,1,n,n*n]:
            _,_,_,beta,theta,mu=parameters(n,m)
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',RuntimeWarning)
                z,_=roots_jacobi(n,m-.5,.5)
            w=1/(float(mu)*2*(1-z))
            assert np.all(w>0)
            assert abs(w.sum()-1)<1e-9,(n,m,w.sum())
            assert abs(np.sum(w*w)-float(beta))<1e-9
            assert max(w)<=8*float(beta)+1e-12
            root_checks+=1
    return {'critical_rows':len(rows),'spectral_rows':len(spectral),
            'free_energy_rows':len(frees),'saddle_rows':len(saddles),
            'root_parameter_pairs':root_checks}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data'))
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    result={'exact':exact_audit(),'numerical':numerical_audit(args.output),
            'versions':{'python':platform.python_version(),
                        'numpy':np.__version__,'scipy':scipy.__version__},
            'status':'All assertions passed. Floating-point outputs are diagnostics.'}
    (args.output/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    main()
