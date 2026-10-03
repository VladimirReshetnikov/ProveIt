#!/usr/bin/env python3
"""Exact coefficient checks and arbitrary-precision saddle diagnostics.

The integer checks are exact. Floating-point diagnostics are not interval
certificates. Run: python verify.py --max-n 5000 --dps 60
"""
from __future__ import annotations
import argparse, csv, json, math, sys
from pathlib import Path
import mpmath as mp

IDS = {1:'A022629',2:'A092484',3:'A265840',4:'A265841',5:'A265842'}
PREFIX = {
1:[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728],
2:[1,1,4,13,25,77,161,393,726,2010,3850,7874,16791,31627,69695,139560],
3:[1,1,8,35,91,405,1069,3799,8686,36744,86310,235776,686329,1605779,5230579,13191702],
4:[1,1,16,97,337,2177,7313,38529,108594,717186,2053522,7527458,30757155,88042387,448973459,1390503396],
5:[1,1,32,275,1267,11925,51445,406183,1406614,14690040,51144366,251885088,1481359033,5108404955,42614629915,158222158038]}

def coefficients(alpha:int, nmax:int)->list[int]:
    """Descending-knapsack multiplication of the Euler product."""
    if alpha<1 or nmax<0: raise ValueError('alpha >= 1 and nmax >= 0 required')
    a=[0]*(nmax+1); a[0]=1
    for k in range(1,nmax+1):
        weight=k**alpha
        for n in range(nmax,k-1,-1): a[n]+=weight*a[n-k]
    return a

def recurrence_coefficients(alpha:int,nmax:int)->list[int]:
    """Independent exact logarithmic-derivative recurrence."""
    b=[0]*(nmax+1)
    for d in range(1,nmax+1):
        power=1
        for j in range(1,nmax//d+1):
            power*=d**alpha
            b[d*j]+=(-1 if j%2==0 else 1)*d*power
    a=[0]*(nmax+1); a[0]=1
    for n in range(1,nmax+1):
        value=sum(b[k]*a[n-k] for k in range(1,n+1))
        assert value % n == 0
        a[n]=value//n
    return a

def cutoff(alpha:int,t:mp.mpf,dps:int)->int:
    """Truncate so a geometric upper bound on sum k^(alpha+6)exp(-tk)
    is below 10^(-dps-10). This is evaluated in floating point, not intervals.
    """
    k=max(20,int(2*(alpha+6)/t))
    tol=mp.power(10,-dps-10)
    while True:
        ratio=mp.exp(-t+(alpha+6)/mp.mpf(k))
        bound=mp.power(k,alpha+6)*mp.exp(-t*k)/(1-ratio)
        if ratio<1 and bound<tol: return k
        k=int(k*1.25)+1

def moments(alpha:int,t:mp.mpf,dps:int, full:bool=False):
    lim=cutoff(alpha,t,dps)
    e=mp.exp(-t); decay=mp.mpf(1)
    total=mp.mpf(0); mean=mp.mpf(0); B=mp.mpf(0)
    k3=mp.mpf(0); k4=mp.mpf(0); k5=mp.mpf(0); k6=mp.mpf(0)
    for k in range(1,lim+1):
        decay*=e; weight=(k**alpha)*decay
        p=weight/(1+weight); v=p*(1-p)
        mean+=k*p; B+=k*k*v
        if full:
            total+=mp.log1p(weight)
            k3+=k**3*v*(1-2*p)
            k4+=k**4*v*(1-6*v)
            k5+=k**5*v*(1-2*p)*(1-12*v)
            k6+=k**6*v*(1-30*v+120*v*v)
    return (total,mean,B,k3,k4,k5,k6,lim) if full else (mean,B)

def saddle(alpha:int,n:int,dps:int):
    K=mp.sqrt(2*n); r=mp.log(K)
    t=alpha*r/K
    for it in range(30):
        mean,B=moments(alpha,t,dps)
        dt=(mean-n)/B
        new=t+dt
        if new<=0: new=t/2
        if abs(new-t)<mp.power(10,-dps+8):
            t=new; break
        t=new
    else: raise ArithmeticError('Newton iteration did not converge')
    F,mean,B,k3,k4,k5,k6,lim=moments(alpha,t,dps,True)
    e1=k4/(8*B**2)-5*k3**2/(24*B**3)
    e2=(-k6/(48*B**3)+7*k3*k5/(48*B**4)+35*k4**2/(384*B**4)
        -35*k3**2*k4/(64*B**5)+385*k3**4/(1152*B**6))
    log_gauss=F+n*t-mp.log(2*mp.pi*B)/2
    return t,log_gauss,e1,e2,mean-n,lim

def log_approx(alpha:int,n:int,order:int)->mp.mpf:
    K=mp.sqrt(2*n); r=mp.log(K); c=mp.pi**2/(6*alpha**2)
    P=[c,c,c-c*c/2,c+mp.mpf(9)/10*c*c,
       c+mp.mpf(41)/5*c*c+c**3/2,
       c+27*c*c+mp.mpf(1973)/210*c**3,
       c+mp.mpf(129)/2*c*c+mp.mpf(8109)/70*c**3-5*c**4/8]
    return alpha*K*(r-1+sum(P[j-1]/r**j for j in range(1,order+1)))

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-n',type=int,default=5000)
    ap.add_argument('--dps',type=int,default=60)
    ap.add_argument('--alpha',type=int,nargs='*',default=[1,2,3,4,5])
    args=ap.parse_args()
    if args.max_n<16 or args.dps<30: ap.error('max-n >= 16, dps >= 30 required')
    mp.mp.dps=args.dps+15
    out=Path(__file__).resolve().parent/'data'; out.mkdir(exist_ok=True)
    rows=[]
    for alpha in args.alpha:
        if alpha not in IDS: ap.error('alpha must be in 1..5')
        a=coefficients(alpha,args.max_n)
        assert a[:len(PREFIX[alpha])]==PREFIX[alpha]
        ncheck=min(150,args.max_n)
        assert a[:ncheck+1]==recurrence_coefficients(alpha,ncheck)
        assert all(a[n+1]>a[n] for n in range(1,args.max_n))
        with (out/f'{IDS[alpha]}_computed.txt').open('w') as f:
            f.write('# Independently computed by verify.py; n a_alpha(n)\n')
            for n,v in enumerate(a):f.write(f'{n} {v}\n')
        print(f'alpha={alpha}: exact checks passed through n={args.max_n}',flush=True)
        sample=sorted({min(100,args.max_n),min(1000,args.max_n),args.max_n})
        for n in sample:
            loga=mp.log(a[n]); t,L,e1,e2,res,lim=saddle(alpha,n,args.dps)
            row={'alpha':alpha,'oeis':IDS[alpha],'n':n,
                 'log_exact':mp.nstr(loga,25),'saddle_t':mp.nstr(t,25),
                 'exact_over_gaussian':mp.nstr(mp.exp(loga-L),22),
                 'exact_over_edgeworth1':mp.nstr(mp.exp(loga-L)/(1+e1),22),
                 'exact_over_edgeworth2':mp.nstr(mp.exp(loga-L)/(1+e1+e2),22),
                 'log_error_0':mp.nstr(loga-log_approx(alpha,n,0),22),
                 'log_error_3':mp.nstr(loga-log_approx(alpha,n,3),22),
                 'log_error_7':mp.nstr(loga-log_approx(alpha,n,7),22),
                 'mean_residual':mp.nstr(res,5),'summation_cutoff':lim}
            rows.append(row);print(row,flush=True)
        with (out/f'diagnostics_alpha{alpha}.csv').open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[-1].keys());w.writeheader()
            w.writerows([r for r in rows if r['alpha']==alpha])
    with (out/'diagnostics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    print('ALL EXACT AND FLOATING-POINT CHECKS COMPLETED.',flush=True)

if __name__=='__main__': main()
