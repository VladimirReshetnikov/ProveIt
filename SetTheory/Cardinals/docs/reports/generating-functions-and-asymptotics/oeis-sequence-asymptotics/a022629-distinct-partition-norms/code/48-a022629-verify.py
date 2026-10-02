#!/usr/bin/env python3
"""Reproduce A022629 exact coefficients and saddle-point diagnostics.
Requires Python 3.10+, mpmath, sympy. Numerical checks are not formal proofs.
"""
from __future__ import annotations
import argparse, csv, json, math
from pathlib import Path
import mpmath as mp

INITIAL = [1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728,2525,3741,5775,8244,12447]

def coefficients(nmax: int, power: int = 1) -> list[int]:
    if not isinstance(nmax, int) or not isinstance(power, int) or nmax < 0 or power < 1:
        raise ValueError('nmax must be nonnegative and power a positive integer')
    a = [1] + [0]*nmax
    for k in range(1,nmax+1):
        w = k**power
        for n in range(nmax,k-1,-1):
            a[n] += w*a[n-k]
    return a

def tail_bound(t: mp.mpf, K: int, exponent: mp.mpf) -> mp.mpf:
    """Upper bound on sum_{k>K} k**exponent * exp(-t*k), exponent>=0."""
    if t <= 0 or K < 0 or exponent < 0:
        raise ValueError('Require t>0, K>=0, and exponent>=0')
    return mp.exp(t)*mp.gammainc(exponent+1,t*(K+1),mp.inf)/t**(exponent+1)

def saddle(n: int, power: mp.mpf = mp.mpf(1), dps: int = 50) -> dict:
    if n < 2 or power <= 0:
        raise ValueError('Require n>=2 and power>0')
    if dps < 20:
        raise ValueError('Use at least 20 decimal digits for saddle diagnostics')
    mp.mp.dps=dps
    x=mp.sqrt(2*n); t=power*mp.log(x)/x
    # Solve first at modest precision; then refine to the requested precision.
    def sums(t, precision, final=False):
        with mp.workdps(precision):
            K=max(20,int((precision*mp.log(10)+(power+6)*mp.log(1+1/t)+20)/t))
            mean=mp.mpf(0); V=mp.mpf(0); S=mp.mpf(0); k3=mp.mpf(0); k4=mp.mpf(0)
            for k in range(1,K+1):
                odds=mp.exp(power*mp.log(k)-t*k)
                p=odds/(1+odds); q=1-p; v=p*q
                mean+=k*p; V+=k*k*v
                if final:
                    S+=mp.log1p(odds)
                    k3+=k**3*v*(1-2*p)
                    k4+=k**4*v*(1-6*v)
            return mean,V,S,k3,k4,K
    for precision in [22,dps]:
        with mp.workdps(precision):
            for _ in range(20):
                mu,V,*_=sums(t,precision)
                step=(mu-n)/V
                if abs(step)<mp.mpf(10)**(-precision+7)*t: break
                new=t+step
                t=new if new>0 else t/2
            else: raise ArithmeticError('Newton iteration did not converge')
    mu,V,S,k3,k4,K=sums(t,dps,True)
    if not t < power/mp.e:
        raise ArithmeticError('Saddle is outside the real upper-transition regime; use a larger n.')
    L=-mp.lambertw(-t/power,-1).real; r=mp.exp(L)
    correction=k4/(8*V**2)-5*k3**2/(24*V**3)
    log_saddle=S+n*t-mp.log(2*mp.pi*V)/2
    return dict(t=t,L=L,r=r,variance=V,log_saddle=log_saddle,
                correction=correction,log_corrected=log_saddle+mp.log1p(correction),
                mean_residual=mu-n,K=K,
                tail_bound_order4=26*tail_bound(t,K,power+4))

def log_expansion(n: int, terms: int=4, power=1):
    x=mp.sqrt(2*n); lam=mp.log(x); A=mp.pi**2/(6*power**2)
    c=[A,A,A-A*A/2,A+mp.mpf(9)/10*A*A,
       A+mp.mpf(41)/5*A*A+A**3/2,
       A+27*A*A+mp.mpf(1973)/210*A**3]
    if not 0<=terms<=len(c): raise ValueError('terms must be between 0 and 6')
    return power*x*(lam-1+sum(c[j]/lam**(j+1) for j in range(terms)))

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--max-n',type=int,default=6400)
    parser.add_argument('--dps',type=int,default=45); args=parser.parse_args()
    if args.max_n<20: parser.error('--max-n must be at least 20')
    if args.dps<20: parser.error('--dps must be at least 20')
    out=Path(__file__).resolve().parent.parent/'data'; out.mkdir(exist_ok=True)
    a=coefficients(args.max_n); assert a[:len(INITIAL)]==INITIAL
    # Independent logarithmic-derivative recurrence, through degree 100.
    lim=min(100,args.max_n); b=[0]*(lim+1)
    for k in range(1,lim+1):
        for j in range(1,lim//k+1): b[k*j]+=(-1)**(j+1)*k**(j+1)
    for n in range(1,lim+1): assert n*a[n]==sum(b[k]*a[n-k] for k in range(1,n+1))
    assert all(a[n+1]>a[n] for n in range(1,args.max_n))
    with (out/'exact_coefficients.csv').open('w',newline='') as f:
        w=csv.writer(f); w.writerow(['n','a(n)']); w.writerows(enumerate(a))
    rows=[]
    for n in [100,400,1600,6400]:
        if n>args.max_n: continue
        v=saddle(n,dps=args.dps); exactlog=mp.log(a[n]);
        row={'n':n,'log_exact':mp.nstr(exactlog,20),
             'relative_error_gaussian':mp.nstr(mp.expm1(v['log_saddle']-exactlog),12),
             'relative_error_corrected':mp.nstr(mp.expm1(v['log_corrected']-exactlog),12),
             'log_error_core':mp.nstr(log_expansion(n,0)-exactlog,12),
             'log_error_4terms':mp.nstr(log_expansion(n,4)-exactlog,12)}
        row.update({k:(v[k] if k=='K' else mp.nstr(v[k],25)) for k in v})
        rows.append(row); print(json.dumps(row),flush=True)
    (out/'numerical_checks.json').write_text(json.dumps(rows,indent=2)+'\n')
    with (out/'saddle_table.tex').open('w') as f:
        for r in rows:
            f.write(f"{r['n']} & {float(r['log_exact']):.8f} & {float(r['relative_error_gaussian']):.3e} & {float(r['relative_error_corrected']):.3e} \\\\\n")
    print('All exact checks passed.',flush=True)

if __name__=='__main__': main()
