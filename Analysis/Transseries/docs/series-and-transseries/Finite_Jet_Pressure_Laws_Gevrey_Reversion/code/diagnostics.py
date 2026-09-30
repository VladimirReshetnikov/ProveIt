#!/usr/bin/env python3
"""Non-certified numerical diagnostics. Requires numpy, scipy, mpmath.
All exact algebraic verification is separately in verify.py.
"""
from __future__ import annotations
import argparse,csv,json,math
from pathlib import Path
import numpy as np
from scipy.special import gammaln,logsumexp
from scipy.optimize import brentq
import mpmath as mp


def pressure(s,theta,a,K):
    # Floating counterpart of the exact coefficient formula.
    A=np.r_[0.,np.asarray(a[:K],float)]
    rec=np.zeros(K+1);rec[0]=1.
    for k in range(1,K+1):rec[k]=theta*sum(A[j]*rec[k-j] for j in range(1,k+1))
    B=np.convolve(np.arange(K+1)*A,rec)[:K+1]
    p=np.zeros(K+1);bp=np.r_[1.,np.zeros(K)]
    for r in range(1,K+1):
        bp=np.convolve(bp,B)[:K+1]
        for k in range(r,K+1):
            rf=math.prod(s*k+u for u in range(r-1))
            p[k]+=rf/math.factorial(r)*bp[k]/k
    return p


def logR(n,s,theta,C=1.,nu=0.):
    js=np.arange(n,dtype=float)
    lw=s*(gammaln(js+nu+1)-gammaln(nu+2));lw[0]=0.
    b=np.zeros(n)
    for k in range(1,n):
        j=js[1:k+1]
        factors=n*j+theta*(k-j)
        if np.any(factors<=0):raise ValueError('Nonpositive recurrence weight')
        terms=np.log(factors)+lw[1:k+1]+lw[k-1::-1]-lw[k]+b[k-1::-1]
        b[k]=math.log(C/k)+logsumexp(terms)
    return b[-1]-math.log(n*C)


def saddle(n,s,theta,C=1.,nu=0.,K=None):
    if K is None: K=max(1,math.floor(1/s+1e-12))
    a=np.array([C*math.exp(s*(gammaln(j+nu+1)-gammaln(nu+2))) for j in range(1,K+1)])
    x=n**(-s)
    def evals(y):
        terms=a*y**np.arange(1,K+1)
        A=terms.sum();B=np.dot(np.arange(1,K+1),terms)/(1-theta*A)
        return A,B
    def fn(y):
        A,B=evals(y)
        return y*(1-B)**s-x if B<1 and 1-theta*A>0 else float('nan')
    lo=x;hi=x
    for _ in range(10000):
        hi*=1.001
        value=fn(hi)
        if math.isnan(value): return float('nan')
        if value>=0:break
    else:return float('nan')
    y=brentq(fn,lo,hi,xtol=1e-15)
    A,B=evals(y)
    lead=-math.log1p(-theta*A)/theta if theta else A
    P=lead+s*(math.log1p(-B)+B)
    return n*P


def mp_logR(n,s,theta,dps=80):
    with mp.workdps(dps):
        s=mp.mpf(s);theta=mp.mpf(theta)
        w=[mp.mpf(1)]+[mp.factorial(j)**s for j in range(1,n)]
        b=[mp.mpf(1)]+[mp.mpf(0)]*(n-1)
        for k in range(1,n):
            b[k]=mp.fsum((n*j+theta*(k-j))*w[j]*b[k-j] for j in range(1,k+1))/k
        return float(mp.log(b[-1]/(n*w[-1])))


def main():
    p=argparse.ArgumentParser();p.add_argument('--max-n',type=int,default=10000)
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=p.parse_args()
    if args.max_n < 100:
        p.error('--max-n must be at least 100')
    args.output.mkdir(exist_ok=True,parents=True)
    rows=[]
    for s in (.5,.4,1/3,.25,.2):
        K=max(1,int(math.floor(1/s+1e-10)))
        a=[math.exp(s*gammaln(j+1)) for j in range(1,K+1)]
        for theta in (-1.,0.,1.):
            coeff=pressure(s,theta,a,K)
            for n in (100,1000,10000):
                if n>args.max_n: continue
                actual=logR(n,s,theta)
                expansion=sum(coeff[k]*n**(1-k*s) for k in range(1,K+1))
                ps=saddle(n,s,theta)
                row={'s':s,'theta':theta,'n':n,'log_R':actual,
                     'finite_jet_log':expansion,'log_residual':actual-expansion,
                     'saddle_log':ps,'saddle_residual':actual-ps}
                rows.append(row)
                print(s,theta,n,'residual=',actual-expansion,flush=True)
    with (args.output/'diagnostics.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
    cross=[]
    for s in ('0.5','0.4','0.333333333333333333333333333333333333333333','0.25','0.2'):
        for theta in (-1,0,1):
            high=mp_logR(70,s,theta)
            low=logR(70,float(s),theta)
            error=abs(high-low)
            assert error<2e-11,(s,theta,error)
            cross.append({'s':s,'theta':theta,'n':70,'absolute_log_difference':error})
    (args.output/'numeric_validation.json').write_text(json.dumps({'status':'passed','certified':False,'cross_checks':cross,'rows':len(rows)},indent=2)+'\n')
    # A small table for the manuscript.
    chosen=[r for r in rows if r['s'] in (1/3,.25) and r['theta']==1]
    lines=['\\begin{tabular}{rrrrr}','\\toprule','$s$ & $n$ & $\\log R_n$ & $\\log R_n-S_n$ & $\\log R_n-nP(n^{-s})$\\\\','\\midrule']
    for r in chosen:
        sv='1/3' if r['s']==1/3 else '1/4'
        saddle_text=f"{r['saddle_residual']:.6f}" if math.isfinite(r['saddle_residual']) else r'\textemdash'
        lines.append(f"${sv}$ & {r['n']:,} & {r['log_R']:.6f} & {r['log_residual']:.6f} & {saddle_text}\\\\")
    lines+=['\\bottomrule','\\end{tabular}']
    (args.output/'numerical_table.tex').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':main()
