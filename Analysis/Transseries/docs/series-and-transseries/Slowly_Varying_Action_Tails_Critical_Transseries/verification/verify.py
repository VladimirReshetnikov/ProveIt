#!/usr/bin/env python3
"""Exact algebra checks and floating-point diagnostics for the accompanying article.

Usage: python verification/verify.py [--quick | --exact-only] [--output-dir PATH]
(ed. 2026-09-29: the default output directory is rerun/ in the package root;
writing into the recorded verification/ needs --overwrite-recorded. Files are
written with LF, and results.json ends with a newline.)
Requires Python 3.10+, numpy, scipy, mpmath, sympy. Numerical results are NOT
interval certificates. The proofs in article.tex do not rely on these checks.
"""
from __future__ import annotations
import argparse, csv, json, math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import mpmath as mp
import sympy as sy
from scipy.special import roots_jacobi
from scipy.integrate import quad

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 65

def exp_series(c: list[F], n: int) -> list[F]:
    """exp(sum_{j>=1} c[j] z^j) through degree n, with c[0]=0."""
    out = [F(1)] + [F(0)] * n
    for k in range(1,n+1):
        out[k] = sum((j*c[j]*out[k-j] for j in range(1,min(k,len(c)-1)+1)),F(0))/k
    return out

def lagrange(a: list[F], beta: F, nmax: int) -> list[F]:
    return [F(0)] + [exp_series([F(0)]+[n*beta*x for x in a[1:]],n)[n]/n
                      for n in range(1,nmax+1)]

def feedback(a: list[F], beta: F, nmax: int) -> list[F]:
    u=[F(0)]*(nmax+1)
    for n in range(1,nmax+1):
        u[n]=sum((beta*a[j]*exp_series([j*v for v in u[:n]],n-j)[n-j]
                  for j in range(1,min(n,len(a)-1)+1)),F(0))
    return u

def exact_checks() -> int:
    count=0
    for beta in [F(1),F(2,3),F(7,5)]:
        a=[F(0)]+[F(1,j*j+1) for j in range(1,17)]
        u=lagrange(a,beta,16); v=feedback(a,beta,16)
        for j in range(17):
            assert u[j]==v[j]; count+=1
        old=[F(0)]*17
        for M in range(1,9):
            w=lagrange(a[:M+1],beta,16)
            for j in range(1,17):
                assert old[j] <= w[j] <= u[j]; count+=1
                if j<=M: assert w[j]==u[j]; count+=1
            old=w
    alpha,m,p1,p2,u=sy.symbols('alpha m p1 p2 u', nonzero=True)
    v1=-p1/alpha
    v2=(alpha+1)*p1**2/(2*alpha**2)-m*p1/alpha**2-p2/alpha
    # Exact coefficient identities for the chart, using truncated binomial rules.
    c1=alpha*v1+p1
    c2=alpha*v2+alpha*(alpha-1)*v1*v1/2+alpha*v1*p1+p2-m*v1
    assert sy.simplify(c1)==0; count+=1
    assert sy.simplify(c2)==0; count+=1
    # Bell-polynomial coefficient recurrence for exp(sum b_r z^r).
    z=sy.symbols('z'); bs=sy.symbols('b1:4')
    E=[sy.Integer(1)]
    for k in range(1,7):
        E.append(sy.expand(sum(r*bs[r-1]*E[k-r] for r in range(1,min(k,3)+1))/k))
    direct=sy.exp(sum(bs[r-1]*z**r for r in range(1,4))).series(z,0,7).removeO()
    for k in range(7): assert sy.expand(E[k]-direct.coeff(z,k))==0; count+=1
    return count

def g_zero(alpha: mp.mpf) -> mp.mpf:
    return mp.gamma(-alpha)**(-1/alpha)/(alpha*mp.gamma(1-1/alpha))

def g_log_coefficient(alpha: mp.mpf, k: int) -> mp.mpf:
    G=mp.gamma(-alpha); psi=mp.digamma(-alpha)
    def f(t):
        if t==0: return mp.mpf('0')
        J=G*(-1j*t)**alpha
        D=J*(psi-mp.log(-1j*t))
        return mp.re(mp.exp(J)*D**k/mp.factorial(k))/mp.pi
    return mp.quad(f,[0,1,3,7,15,30,mp.inf])

def probability(n: int, beta: float, d0: float, alpha: float,
                m: int, M: int | None = None) -> float:
    """FFT coefficient, with radius e^(-2/n), oversampling >=32 n.
    Exact coefficient depends only on weights through min(M,n). d0 is the
    FULL A(1), so a cutoff computes P(K=n, no action>M), not a renormalized law.
    """
    if n<1: raise ValueError('n must be positive')
    size=1 << (32*n-1).bit_length()
    r=math.exp(-2/n)
    cap=n if M is None else min(n,max(0,M))
    coeff=np.zeros(size)
    j=np.arange(1,cap+1,dtype=float)
    weights=np.log(j)**m/j**(1+alpha)
    if cap: weights[0]=1.0 # replace the zero logarithmic weight at j=1
    coeff[1:cap+1]=weights*np.exp(-2*j/n)
    Ftheta=np.exp(n*beta*(np.fft.fft(coeff)-d0))
    val=np.fft.ifft(Ftheta)[n].real*math.exp(2)
    if val < -1e-12: raise ArithmeticError('unexpected negative coefficient')
    return float(val)

def exprel2(z: np.ndarray) -> np.ndarray:
    out=np.empty_like(z,dtype=complex)
    small=np.abs(z)<1e-3
    w=z[small]
    out[small]=.5+w/6+w*w/24+w**3/120+w**4/720+w**5/5040
    w=z[~small]
    out[~small]=(np.expm1(w)-w)/(w*w)
    return out

def cutoff_density(alpha: float, s: float, lam: float, nodes: int=96) -> float:
    if not (1<alpha<2 and s>0): raise ValueError('1<alpha<2, s>0 required')
    x,w=roots_jacobi(nodes,0,1-alpha)
    x=(x+1)/2; w=w/2**(2-alpha)
    kappa=s**(-alpha)/alpha
    mu=s**(1-alpha)/(alpha-1)
    def integrand(t):
        z=1j*t*s*x
        J=-kappa-1j*t*mu-t*t*s**(2-alpha)*np.dot(w,exprel2(z))
        return float(np.real(np.exp(J-1j*t*lam))/math.pi)
    # At these diagnostic parameters the discarded tail is exponentially tiny.
    return quad(integrand,0,36,epsabs=2e-12,epsrel=2e-11,limit=300)[0]

def cutoff_profile(alpha: float, s: float, lam: float=0.0) -> float:
    if lam != 0: raise NotImplementedError('table normalization uses lambda=0')
    return cutoff_density(alpha,s,lam)/float(g_zero(mp.mpf(alpha)))

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--quick',action='store_true',help='Use fewer coefficient indices')
    parser.add_argument('--exact-only',action='store_true',help='Run exact checks without changing data files')
    parser.add_argument('--output-dir',type=Path,default=ROOT.parent/'rerun',help='Destination for JSON and CSV outputs')
    parser.add_argument('--overwrite-recorded',action='store_true',help='Allow writing into the recorded verification/ directory')
    args=parser.parse_args()
    if (not args.exact_only and args.output_dir.resolve()==ROOT.resolve()
            and not args.overwrite_recorded):
        parser.error('refusing to overwrite the recorded verification/ outputs; '
                     'pass --overwrite-recorded or choose another --output-dir')
    checks=exact_checks()
    if args.exact_only:
        print(f'{checks} exact algebra assertions passed; no data files changed.')
        return
    outdir=args.output_dir.resolve()
    outdir.mkdir(parents=True,exist_ok=True)
    alpha=mp.mpf('1.5'); m=1
    d0=1-mp.diff(mp.zeta,1+alpha)
    d1=1-mp.diff(mp.zeta,alpha)
    beta=1/d1; C=beta*mp.gamma(-alpha)
    g0=g_zero(alpha); dg=mp.diff(g_zero,alpha); c2=g_log_coefficient(alpha,2)
    c3=g_log_coefficient(alpha,3); c4=g_log_coefficient(alpha,4)
    constants={k:mp.nstr(v,45) for k,v in
               {'alpha':alpha,'beta_c':beta,'d0':d0,'d1':d1,'g0':g0,
                'minus_g_derivative':-dg,'second_log_coefficient':c2,'third_log_coefficient':c3,'fourth_log_coefficient':c4}.items()}
    ns=[256,1024,4096] if args.quick else [256,1024,4096,16384,65536]
    rows=[]; cutoff_rows=[]
    for n in ns:
        L=-m/alpha*mp.lambertw(-alpha/m*(n*beta)**(-mp.mpf(1)/m),-1)
        b=mp.exp(L)
        p=probability(n,float(beta),float(d0),float(alpha),m)
        obs=float(b)*p
        first=g0-m*dg/L
        second=first+c2/L**2
        third=second+c3/L**3; fourth=third+c4/L**4
        rows.append({'n':n,'b':float(b),'log_b':float(L),'b_times_p':obs,
                     'leading':float(g0),'first':float(first),'second':float(second),'third':float(third),'fourth':float(fourth)})
        if n in [1024,4096,16384,65536]:
            for s in [0.75,1.0,1.5,2.0]:
                M=int(float(b)*s); actual_s=M/float(b)
                pcut=probability(n,float(beta),float(d0),float(alpha),m,M)
                prof=cutoff_profile(float(alpha),actual_s)
                h=2e-5
                da=(cutoff_profile(float(alpha)+h,actual_s)-
                    cutoff_profile(float(alpha)-h,actual_s))/(2*h)
                corrected=prof-m*da/float(L)
                cutoff_rows.append({'n':n,'M':M,'s':actual_s,'actual_ratio':pcut/p,
                                    'profile':prof,'first':corrected})
    # Independent positive recurrence at n=256 (65-digit arithmetic).
    nn=256
    weights=[mp.mpf(0)]+[mp.log(j)/mp.mpf(j)**(1+alpha) for j in range(1,nn+1)]
    weights[1]=mp.mpf(1)
    probs=[mp.exp(-nn*beta*d0)]+[mp.mpf(0)]*nn
    for k in range(1,nn+1):
        probs[k]=nn*beta/k*mp.fsum(j*weights[j]*probs[k-j] for j in range(1,k+1))
    fft_p=probability(nn,float(beta),float(d0),float(alpha),m)
    relative_fft_error=abs(mp.mpf(fft_p)/probs[nn]-1)
    assert relative_fft_error < mp.mpf('1e-10')
    jacobi_error=max(abs(cutoff_density(float(alpha),s,0,96)-
                        cutoff_density(float(alpha),s,0,160)) for s in [.75,1.,1.5,2.])
    assert jacobi_error < 1e-9
    # Real critical inverse for m=1: exact polylog parameter derivative.
    inverse=[]
    psi=mp.digamma(-alpha)
    for L in [8,12,20,35]:
        T=mp.exp(-L); eps=C*T**alpha*L
        def A(x): return mp.exp(-x)-mp.diff(lambda z:mp.polylog(z,mp.exp(-x)),1+alpha)
        def E(x): return x+beta*(A(x)-d0)
        root=mp.findroot(lambda v:(E(T*v)-eps)/eps,(mp.mpf('.9'),mp.mpf('1.1')))
        v1=-psi/alpha
        v2=(alpha+1)*psi**2/(2*alpha**2)-psi/alpha**2
        inverse.append({'L':L,'x_over_T':mp.nstr(root,35),
                        'first':mp.nstr(1+v1/L,35),
                        'second':mp.nstr(1+v1/L+v2/L**2,35)})
    for name,data in [('coefficients',rows),('cutoffs',cutoff_rows),('inverse',inverse)]:
        with (outdir/(name+'.csv')).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=data[0].keys(),lineterminator='\n');writer.writeheader();writer.writerows(data)
    output={'exact_assertions_passed':checks,'constants':constants,
            'numerical_status':'Floating-point diagnostics, not interval certificates.',
            'fft_relative_error_against_65_digit_recurrence':mp.nstr(relative_fft_error,12),
            'jacobi_96_vs_160_max_difference':jacobi_error,
            'coefficient_rows':rows,'cutoff_rows':cutoff_rows,'inverse_rows':inverse}
    (outdir/'results.json').write_text(json.dumps(output,indent=2)+'\n',newline='\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__': main()
