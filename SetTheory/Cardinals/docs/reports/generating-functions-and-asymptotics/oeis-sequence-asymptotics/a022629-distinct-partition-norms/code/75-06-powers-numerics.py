"""Exact checks and floating-point saddle estimates for weighted distinct partitions."""
from __future__ import annotations
import json,math,time
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.special import expit,lambertw
BASE=Path(__file__).resolve().parent

def exact_coefficients(nmax:int,r:int=1,s:int=1)->list[int]:
    if any(type(x) is not int for x in (nmax,r,s)) or nmax<0 or r<1 or s<1:
        raise ValueError('nmax >= 0 and integer r,s >= 1 are required')
    a=[1]+[0]*nmax
    for k in range(1,nmax+1):
        w=k**r
        for _ in range(s):
            for n in range(nmax,k-1,-1):a[n]+=w*a[n-k]
    return a

def saddle(n:float,r:float=1,s:int=1)->dict[str,float]:
    if not math.isfinite(n) or not math.isfinite(r) or n<=0 or r<=0 or type(s) is not int or s<1:
        raise ValueError('n,r must be finite and positive; s must be a positive integer')
    m=math.sqrt(2*n/s);L=math.log(max(m,3))
    t0=r*L/m
    def sums(t,full=False):
        K=float((-r/t*lambertw(-t/r,-1)).real) if t<r/math.e else max(1.,r/t)
        cutoff=max(100,int(K+(65+abs(r)*math.log(max(K,2)))/t))
        # Chunking controls memory even at n=1e10 or higher.
        values=np.zeros(5 if full else 1)
        for start in range(1,cutoff+1,200000):
            k=np.arange(start,min(cutoff+1,start+200000),dtype=float)
            z=r*np.log(k)-t*k;p=expit(z)
            values[0]+=s*np.sum(k*p)
            if full:
                pq=expit(z)*expit(-z)
                values[1]+=s*np.sum(np.logaddexp(0,z))
                values[2]+=s*np.sum(k*k*pq)
                values[3]+=s*np.sum(k**3*pq*(1-2*p))
                values[4]+=s*np.sum(k**4*pq*(1-6*pq))
        return values
    lo=t0/2;hi=t0*2
    while sums(lo)[0]<n:lo/=2
    while sums(hi)[0]>n:hi*=2
    t=brentq(lambda t:sums(t)[0]-n,lo,hi,xtol=1e-15*t0,rtol=1e-14)
    mass,F,k2,k3,k4=sums(t,True)
    if t>=r/math.e:
        raise ValueError('This diagnostic requires a saddle with t < r/e (a real large boundary).')
    K=float((-r/t*lambertw(-t/r,-1)).real)
    q1=k4/(8*k2*k2)-5*k3*k3/(24*k2**3)
    logmain=F+n*t-.5*math.log(2*math.pi*k2)
    u=math.pi**2/r**2
    cs=[u/6,u/6,u*(12-u)/72,u*(3*u+20)/120,u*(5*u*u+492*u+360)/2160]
    logseries=[s*r*m*(L-1+sum(cs[j-1]/L**j for j in range(1,M+1))) for M in [0,1,2,3,4,5]]
    return dict(n=n,r=r,s=s,t=t,K=K,v=math.log(K),mass_residual=(mass-n)/n,
                kappa2=k2,kappa3=k3,kappa4=k4,Q1=q1,log_saddle=logmain,
                log_edgeworth=logmain+math.log1p(q1),log_series=logseries)

if __name__=='__main__':
    start=time.time();a=exact_coefficients(10000)
    expected=[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728,2525,3741,5775,8244,12447]
    assert a[:len(expected)]==expected
    assert all(a[n+1]>a[n] for n in range(1,len(a)-1))
    (BASE/'a022629_exact.json').write_text(json.dumps({str(n):str(a[n]) for n in [0,1,2,3,4,5,6,10,20,50,100,200,500,1000,2000,5000,10000]},indent=2))
    rows=[]
    for n in [100,200,500,1000,2000,5000,10000,10**6,10**8,10**10]:
        row=saddle(n)
        if n<=10000:
            lex=math.log(a[n]);row['log_exact']=lex
            row['relative_saddle_error']=math.expm1(row['log_saddle']-lex)
            row['relative_edgeworth_error']=math.expm1(row['log_edgeworth']-lex)
        m=math.sqrt(2*n);L=math.log(m)
        row['first_correction_diagnostic']=L/m*(row.get('log_exact',row['log_edgeworth'])-m*(L-1))
        rows.append(row)
        print(n, 'Q1',row['Q1'],'relative errors',row.get('relative_saddle_error'),row.get('relative_edgeworth_error'),'scaled correction',row['first_correction_diagnostic'],flush=True)
    for r,s in [(1,2),(1,3),(2,1)]:
        b=exact_coefficients(500,r,s);row=saddle(500,r,s);lex=math.log(b[500]);row['log_exact']=lex
        row['relative_saddle_error']=math.expm1(row['log_saddle']-lex);row['relative_edgeworth_error']=math.expm1(row['log_edgeworth']-lex)
        rows.append(row)
    (BASE/'numerical_results.json').write_text(json.dumps(rows,indent=2))
    print('Finished seconds',time.time()-start,flush=True)
