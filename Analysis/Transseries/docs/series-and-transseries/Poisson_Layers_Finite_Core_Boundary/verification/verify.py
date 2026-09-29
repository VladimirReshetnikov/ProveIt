#!/usr/bin/env python3
"""Exact identities and floating-point diagnostics for Poisson feedback layers.

The exact checks use fractions and two independent coefficient algorithms.
The numerical tables are diagnostics, NOT interval-certified error bounds.
Run: python verification/verify.py --output verification/results
Dependencies: Python 3.10+, numpy, scipy. No network access is required.
"""
from __future__ import annotations
import argparse, csv, json, math, platform
from fractions import Fraction as F
from pathlib import Path
from typing import Iterator
import numpy as np
from scipy.optimize import root, brentq
from scipy.special import logsumexp


def partitions(n: int, least: int = 1) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
    else:
        for j in range(least, n + 1):
            for rest in partitions(n - j, j):
                yield (j,) + rest


def partition_coefficient(n: int, p: int, marker_degree: int = 2,
                          marker: int = 1, cutoff: int | None = None) -> F:
    ans = F(0)
    for parts in partitions(n):
        if cutoff is not None and sum(j > cutoff for j in parts) != 1:
            continue
        counts = {j: parts.count(j) for j in set(parts)}
        den = math.prod(math.factorial(c) for c in counts.values())
        ans += F(marker ** counts.get(marker_degree, 0)
                 * sum(j**p for j in parts) ** (len(parts) - 1), den)
    return ans


def exact_triangle(N: int, p: int, weights: list[F]) -> tuple[list[F], list[list[F]]]:
    E = [[F(0)] * (N+1) for _ in range(N+1)]
    for j in range(1, N+1): E[j][0] = F(1)
    u = [F(0)] * (N+1)
    for n in range(1, N+1):
        u[n] = sum((weights[j]*E[j][n-j] for j in range(1,n+1)), F(0))
        for j in range(1,N-n+1):
            E[j][n] = F(j**p,n)*sum((k*u[k]*E[j][n-k]
                                           for k in range(1,n+1)), F(0))
    return u, E


def exact_one_tail(N: int, p: int, M: int) -> list[F]:
    _, E = exact_triangle(N,p,[F(int(1 <= j <= M)) for j in range(N+1)])
    P, T, R = [F(0)]*(N+1), [F(0)]*(N+1), [F(0)]*(N+1)
    R[0]=F(1)
    for n in range(1,N+1):
        P[n]=sum((j**p*E[j][n-j] for j in range(1,min(n,M)+1)),F(0))
        T[n]=sum((E[j][n-j] for j in range(M+1,n+1)),F(0))
        R[n]=sum((P[k]*R[n-k] for k in range(1,n+1)),F(0))
    return [sum((R[k]*T[n-k] for k in range(n+1)),F(0)) for n in range(N+1)]


def exact_checks(N: int = 16) -> dict:
    checks=0
    samples={}
    for p in (2,3):
        for d in (2,3):
            for s in (0,1,2):
                weights=[F(0)]+[F(s if j==d else 1) for j in range(1,N+1)]
                u,_=exact_triangle(N,p,weights)
                for n in range(1,N+1):
                    assert u[n] == partition_coefficient(n,p,d,s)
                    checks+=1
        for M in (1,2,3):
            w=exact_one_tail(N,p,M)
            for n in range(1,N+1):
                assert w[n] == partition_coefficient(n,p,cutoff=M)
                checks+=1
        u,_=exact_triangle(N,p,[F(0)]+[F(1)]*N)
        samples[str(p)]=[str(x) for x in u[1:9]]
    return {'assertions':checks, 'maximum_degree':N,
            'passed':True,'sample_forward_coefficients':samples}


def log_triangle(N: int, a: float, p: float, weights: np.ndarray
                 ) -> tuple[np.ndarray,np.ndarray]:
    if N < 1 or a <= 0 or p <= 1 or np.any(weights < 0):
        raise ValueError('Need N>=1, a>0, p>1 and nonnegative weights')
    E=np.full((N+1,N+1),-np.inf); E[1:,0]=0.0
    u=np.full(N+1,-np.inf)
    logw=np.full(N+1,-np.inf)
    nz=weights>0; logw[nz]=np.log(weights[nz])
    loglam=np.full(N+1,-np.inf)
    loglam[1:]=math.log(a)+p*np.log(np.arange(1,N+1,dtype=float))
    for n in range(1,N+1):
        js=np.arange(1,n+1)
        u[n]=logsumexp(logw[js]+E[js,n-js])
        J=N-n
        if J:
            terms=np.log(np.arange(1,n+1,dtype=float))+u[1:n+1]
            E[1:J+1,n]=loglam[1:J+1]-math.log(n)+logsumexp(
                E[1:J+1,:n][:,::-1]+terms[None,:],axis=1)
    return u,E


def log_one_tail(N:int,a:float,p:float,M:int) -> np.ndarray:
    weights=np.zeros(N+1); weights[1:M+1]=1
    _,E=log_triangle(N,a,p,weights)
    P=np.full(N+1,-np.inf); T=P.copy(); R=P.copy(); R[0]=0
    for n in range(1,N+1):
        js=np.arange(1,min(n,M)+1)
        P[n]=logsumexp(math.log(a)+p*np.log(js)+E[js,n-js])
        js=np.arange(M+1,n+1)
        if len(js): T[n]=logsumexp(E[js,n-js])
        R[n]=logsumexp(P[1:n+1]+R[n-1::-1])
    W=np.full(N+1,-np.inf)
    for n in range(1,N+1): W[n]=logsumexp(R[:n]+T[n:0:-1])
    return W


def saddle(n:float,a:float,p:float,M:int) -> dict[str,float]:
    if n <= M+1: raise ValueError('Saddle diagnostic requires n>M+1')
    def bare(r):
        return math.log(r)+(p-1)*math.log1p(r)+p*r-math.log(a)-(p-1)*math.log(n)
    r=brentq(bare,1e-14,max(100.0,math.log(n)*2))
    z0=n/(1+r); t0=math.exp(-p*r)
    lam=a*np.arange(1,M+1,dtype=float)**p
    degrees=np.arange(1,M+1,dtype=float)
    def components(v):
        t,u,z=np.exp(v)
        terms=np.exp(degrees*math.log(t)+lam*u)
        phi=terms.sum(); phiu=np.dot(lam,terms)
        phit=np.dot(degrees,terms)/t
        gp=phit/(1-phiu)
        return t,u,z,terms,phi,phiu,phit,gp
    def fun(v):
        with np.errstate(over='ignore',invalid='ignore'):
            t,u,z,terms,phi,phiu,phit,gp=components(v)
            return [phi/u-1,(math.log(t)+a*p*z**(p-1)*u)/max(1,abs(math.log(t))),
                    (z+a*z**p*t*gp)/n-1]
    sol=root(fun,np.log([t0,t0,z0]),tol=1e-11)
    residual=float(np.max(np.abs(fun(sol.x))))
    if residual>1e-8: raise RuntimeError(f'Saddle failed: {sol.message}, residual {residual}')
    t,u,z,terms,phi,phiu,phit,gp=components(sol.x)
    if not(0<phiu<1 and z<n): raise RuntimeError('Wrong implicit branch')
    phitt=np.dot(degrees*(degrees-1),terms)/t**2
    phitu=np.dot(degrees*lam,terms)/t
    phiuu=np.dot(lam**2,terms)
    gpp=(phitt+2*phitu*gp+phiuu*gp**2)/(1-phiu)
    k=n-z; Lam=a*z**p
    B=Lam*(t*gp+t*t*gpp); A=a*p*(p-1)*z**(p-2)*u; C=1+p*k/z
    Delta=C*C-A*B
    if Delta<=0: raise RuntimeError('Nonpositive saddle determinant')
    logA= -math.log1p(-phiu)+Lam*u-k*math.log(t)-.5*math.log(Delta)
    return {'n':n,'a':a,'p':p,'M':M,'z':float(z),'tau':float(t),
            'mu':float(k*t**M),'nu':float((n-z0)*math.exp(-M*p*r)),'r':float(r),'log_A':float(logA),'sigma':float(math.sqrt(B/Delta)),
            'residual':residual}


def calibrated_p(n:int,a:float,M:int,target:float) -> float:
    # Choose the p producing the desired finite-n saddle intensity; this is not
    # the same as substituting the leading logarithmic critical-window formula.
    low=1+1/(M+1)+.03
    high=2+1/M
    f=lambda p: math.log(saddle(n,a,p,M)['mu']/target)
    if f(low)*f(high)>=0: raise RuntimeError('Calibration bracket failed')
    return brentq(f,low,high,xtol=2e-12)


def diagnostics() -> list[dict]:
    rows=[]
    for M in (1,2):
        for N in (80,160,320):
            a=1.0; p=calibrated_p(N,a,M,0.5)
            sd=saddle(N,a,p,M)
            weights=np.ones(N+1); weights[0]=0
            full,_=log_triangle(N,a,p,weights)
            zero_weights=weights.copy(); zero_weights[M+1]=0
            zero,_=log_triangle(N,a,p,zero_weights)
            w=log_one_tail(N,a,p,M)
            rows.append({'M':M,'n':N,'p':p,'mu':sd['mu'],'nu':sd['nu'],
                         'prob_no_d':math.exp(zero[N]-full[N]),
                         'one_tail_fraction':math.exp(w[N]-full[N]),
                         'poisson_prediction':math.exp(-sd['nu']),
                         'log_correction_residual':float(full[N]-w[N]-sd['nu']),
                         'full_saddle_relative_ratio':math.exp(full[N]-sd['log_A']-sd['nu'])})
    return rows


def boundary_saddles() -> list[dict]:
    rows=[]
    for M in (1,2,3):
        theta=-math.log((M+1)**(M+1)) # a=1: limiting intensity 1
        for n in (1e6,1e12,1e24,1e48):
            L=math.log(n)
            p=1+1/M+((M+1)*math.log(L)+theta)/(M*L)
            d=saddle(n,1,p,M)
            rows.append({'M':M,'n':n,'p':p,'mu':d['mu'],'nu':d['nu'],'limit_mu':1.0,
                         'core_fraction_prediction':math.exp(-d['mu']),
                         'limit_fraction':math.exp(-1)})
    return rows


def save_csv(path:Path, rows:list[dict]) -> None:
    # Editorial amendment (ProveIt, 2026-09-29): LF line endings on every platform.
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)


def main() -> None:
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='verification/results')
    ap.add_argument('--exact-only',action='store_true'); args=ap.parse_args()
    out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    exact=exact_checks()
    # Cross-check the log-domain algorithm against independent exact coefficients.
    log_errors=[]
    for p in (2,3):
        exact_u,_=exact_triangle(16,p,[F(0)]+[F(1)]*16)
        weights=np.ones(17);weights[0]=0
        logs,_=log_triangle(16,1,p,weights)
        for n in range(1,17):
            ref=math.log(exact_u[n].numerator)-math.log(exact_u[n].denominator)
            log_errors.append(abs(logs[n]-ref))
            assert abs(logs[n]-ref)<1e-11
    exact['floating_crosschecks']=len(log_errors)
    exact['maximum_log_discrepancy']=max(log_errors)
    exact['python']=platform.python_version()
    (out/'exact_checks.json').write_text(json.dumps(exact,indent=2)+'\n',newline='\n')
    print(json.dumps(exact,indent=2))
    if not args.exact_only:
        rows=diagnostics(); save_csv(out/'coefficient_diagnostics.csv',rows)
        save_csv(out/'critical_window_saddles.csv',boundary_saddles())
        for row in rows:print(row)

if __name__=='__main__': main()
