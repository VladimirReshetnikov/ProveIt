#!/usr/bin/env python3
"""Reproduce the numerical and exact checks in the accompanying article.

Python >= 3.11 with the pinned environment; dependencies: mpmath, sympy, matplotlib, numpy.
No network access is used. Output is written to ../data and ../figures.
The analytic theorems do not rely on floating-point root finding. Numerical
roots below are approximations, not interval-arithmetic certificates.

Usage: python code/verify.py [--dps 60] [--roots] [--figures]
The --roots option also performs the more expensive Mellin quadratures.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

class Completion:
    def __init__(self, dps: int = 60):
        if dps < 35:
            raise ValueError('Use at least 35 decimal digits.')
        mp.mp.dps = dps
        self.dps = dps
        self.L = mp.log(2)
        self.tol = mp.power(10, -dps-8)
        self.harmonics = max(10, dps // 5 + 3)
        self.constant = -self.L/12 - (mp.pi**2/12-mp.euler**2/2-mp.stieltjes(1))/self.L
        self.log_coeff = {}
        for k in range(1, self.harmonics + 1):
            z = 2j*mp.pi*k/self.L
            # The exact dyadic resonances are ill-conditioned for eta-based
            # evaluation of zeta. Force the Euler--Maclaurin implementation.
            self.log_coeff[k] = -mp.gamma(z)*mp.zeta(1+z, method='euler-maclaurin')/self.L
        count = 4*self.harmonics + 64
        values = [mp.exp(self.log_profile(self.L*j/count)) for j in range(count)]
        self.coeff = {
            k: mp.fsum(values[j]*mp.exp(-2j*mp.pi*k*j/count) for j in range(count))/count
            for k in range(-8,9)
        }
        self.qnorm = self.raw_q(0)
        self.C0 = mp.re(mp.sqrt(2*mp.pi*self.L)*mp.exp(self.L/8)*self.qnorm)

    def log_phi(self, t):
        """Stable log Phi(t), t > 0, from finite factors and a Bernoulli tail."""
        if t <= 0:
            raise ValueError('t must be positive.')
        v = mp.mpf(t)
        out = mp.mpf(0)
        while v > 1:
            v /= 2
            out += mp.log(-mp.expm1(-v)/v)
        out -= v/2
        for r in range(1, self.dps + 10):
            term = mp.bernoulli(2*r)*v**(2*r)/(2*r*mp.factorial(2*r)*(2**(2*r)-1))
            out += term
            if abs(term) < self.tol:
                break
        else:
            raise ArithmeticError('Bernoulli tail did not converge to target precision.')
        return out

    def log_p(self, t):
        if t <= 0:
            raise ValueError('t must be positive.')
        out = mp.mpf(0)
        v = mp.mpf(t)
        cutoff = (self.dps+12)*mp.log(10)
        while v < cutoff:
            out += mp.log(-mp.expm1(-v))
            v *= 2
        return out

    def log_k(self, t):
        return self.log_p(t) + self.log_phi(t)

    def log_profile(self, v):
        return self.constant + 2*mp.re(mp.fsum(
            c*mp.exp(-2j*mp.pi*k*v/self.L) for k,c in self.log_coeff.items()))

    def raw_q(self, s):
        return mp.fsum(self.coeff[k]*mp.exp(
            -2*mp.pi**2*k*k/self.L+2j*mp.pi*k*(s+mp.mpf('0.5')))
            for k in self.coeff)

    def C(self, s):
        return self.C0*mp.exp(self.L*(s*s+s)/2)*self.raw_q(s)/self.qnorm

    def q_root(self):
        alpha = self.coeff[-1]/self.coeff[0]*mp.exp(-2*mp.pi**2/self.L)
        guess = -mp.mpf('0.5') + mp.log(-1/alpha)/(-2j*mp.pi)
        guess = mp.mpc(mp.re(guess) % 1, mp.im(guess))
        return mp.findroot(self.raw_q, (guess, guess+mp.mpf('0.01')),
                           tol=mp.power(10,-self.dps+12))

    def mellin(self, s, m=None, a=mp.mpf('0.5'), direct=False):
        """C(s), or F_{m,a}(s), by quadrature on the logarithmic axis.

        The finite integration interval is enlarged with precision. Its tails
        have a Gaussian majorant from the proven periodic-profile identity.
        direct=True uses products, independently of the Fourier formula.
        """
        vcenter = self.L*(mp.re(s)+mp.mpf('0.5'))
        width = mp.sqrt(2*self.L*(self.dps+15)*mp.log(10)) + 3
        left = min(-width, vcenter-width)
        right = max(width, vcenter+width)
        points = [left,-8,-4,0,4,8,right]
        points = sorted(set(p for p in points if left <= p <= right))
        h = None if m is None else mp.power(2,-m)
        def integrand(v):
            if direct:
                lk = self.log_k(mp.exp(v))
            else:
                lk = -v*v/(2*self.L)+v/2+self.log_profile(v)
            if h is not None:
                t = h*mp.exp(v)
                lk += -a*t-self.log_phi(t)
            return mp.exp(s*v+lk)
        return mp.quad(integrand, points)

def exact_coefficients(count=8):
    x = sp.Symbol('x')
    log_series = -sum(sp.bernoulli(2*r)*x**r/
        (2*r*sp.factorial(2*r)*(2**(2*r)-1)) for r in range(1,count))
    polynomial = sp.series(sp.exp(log_series),x,0,count).removeO().expand()
    return [sp.factor((-1)**r*polynomial.coeff(x,r)*2**(2*r*r+r))
            for r in range(count)]

def qbinomial(n,k):
    return sp.prod(2**(n-j)-1 for j in range(k))/sp.prod(2**(j+1)-1 for j in range(k))

def exact_checks():
    x=sp.Symbol('x')
    for d in range(1,7):
        matrix=sp.Matrix(d,d,lambda i,j:2**((i+j)*(i+j+1)//2))
        wanted=2**(d*d*(d-1)//2)*sp.prod((2**k-1)**(d-k) for k in range(1,d))
        assert matrix.det()==wanted
    for n in range(1,7):
        p=[(-1)**(n-k)*2**(n*(n-k))*qbinomial(n,k) for k in range(n+1)]
        for j in range(n):
            assert sum(p[k]*2**((k+j)*(k+j+1)//2) for k in range(n+1))==0
    return True

def make_figures(model, A, root):
    import numpy as np
    import matplotlib.pyplot as plt
    out=ROOT/'figures';out.mkdir(exist_ok=True)
    u=np.linspace(0,1,401)
    profile=np.array([float((mp.exp(model.log_profile(model.L*float(v))-model.constant)-1)*10**6) for v in u])
    fig,ax=plt.subplots(figsize=(7.2,3.8))
    ax.plot(u,profile)
    ax.set_xlabel(r'$v/\log 2$');ax.set_ylabel(r'$10^6[H(v)/\exp(c_*)-1]$')
    ax.grid(True,alpha=.25);fig.tight_layout();fig.savefig(out/'periodic_profile.pdf');plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.2,3.8))
    for m in [2,4,6,8]:
        # Coefficients through order 12 are inexpensive via the exponential
        # coefficient recurrence, using exact rational numbers.
        coeff=[sp.Rational(1)]
        ell=[sp.Rational(0)]+[(-1)**(r+1)*sp.bernoulli(2*r)/
             (2*r*sp.factorial(2*r)*(2**(2*r)-1)) for r in range(1,13)]
        for n in range(1,13): coeff.append(sp.factor(sum(k*ell[k]*coeff[n-k] for k in range(1,n+1))/n))
        logs=[float(mp.log10(mp.mpf(str(c.p))/mp.mpf(str(c.q)))+(2*r*r+r-2*m*r)*mp.log10(2)) for r,c in enumerate(coeff)]
        ax.plot(range(13),logs,marker='.',label=f'm = {m}')
    ax.set_xlabel('Truncation order N');ax.set_ylabel(r'$\log_{10}(A_N\,4^{-mN})$')
    ax.legend();ax.grid(True,alpha=.25);fig.tight_layout();fig.savefig(out/'remainder_bounds.pdf');plt.close(fig)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--roots',action='store_true')
    parser.add_argument('--figures',action='store_true')
    args=parser.parse_args()
    print('Building completion',flush=True)
    model=Completion(args.dps)
    A=exact_coefficients()
    root=model.q_root()
    result={'precision':args.dps,'C0':mp.nstr(model.C0,50),
            'C_zero_real':mp.nstr(mp.re(root),45),'C_zero_imag':mp.nstr(mp.im(root),45),
            'A':[str(v) for v in A],'exact_checks':exact_checks(),
            'log_profile_product_errors':[]}
    for v in [0,model.L/3,model.L]:
        direct=v*v/(2*model.L)-v/2+model.log_k(mp.exp(v))
        result['log_profile_product_errors'].append(mp.nstr(direct-model.log_profile(v),8))
    print('Checking direct quadratures',flush=True)
    result['C0_direct_product_error']=mp.nstr(model.mellin(0,direct=True)-model.C0,8)
    result['C_zero_direct_product_residual']=mp.nstr(model.mellin(root,direct=True),8)
    result['C_scaling_error']=mp.nstr(model.C(mp.mpc('.3','2.1')+1)-
            2**(mp.mpc('.3','2.1')+1)*model.C(mp.mpc('.3','2.1')),8)
    result['ratios']=[]
    for m in [0,2,4,6,8]:
        print('Ratio m=',m,flush=True)
        ratio=mp.re(model.mellin(0,m))/model.C0
        result['ratios'].append({'m':m,'ratio':mp.nstr(ratio,40)})
        for n in range(1,len(A)):
            partial=mp.fsum((-1)**r*(mp.mpf(str(A[r].p))/mp.mpf(str(A[r].q)))*mp.power(4,-m*r) for r in range(n))
            rem=(-1)**n*(ratio-partial)
            bound=(mp.mpf(str(A[n].p))/mp.mpf(str(A[n].q)))*mp.power(4,-m*n)
            assert -mp.mpf('1e-45')<=rem<=bound+mp.mpf('1e-45')
    if args.roots:
        result['Dirichlet_zeros']=[]
        for m in [4,6,8]:
            print('Solving zero m=',m,flush=True)
            f=lambda z:model.mellin(z,m)
            # A secant iteration in normalized coordinates prevents overflow.
            z0,z=root,root+mp.mpf('0.0001')
            f0,f1=f(z0),f(z)
            for iteration in range(12):
                nz=z-f1*(z-z0)/(f1-f0)
                if abs(nz-z)<mp.power(10,-args.dps+15):
                    z=nz
                    break
                z0,z=z,nz
                f0,f1=f1,f(z)
            entry={'m':m,'zero_real':mp.nstr(mp.re(z)-m,38),
                   'zero_imag':mp.nstr(mp.im(z),38),
                   'distance_to_lattice':mp.nstr(abs(z-root),18),
                   'normalized_residual':mp.nstr(abs(f(z)),8)}
            result['Dirichlet_zeros'].append(entry)
            print(json.dumps(entry),flush=True)
    if args.figures:make_figures(model,A,root)
    (ROOT/'data').mkdir(exist_ok=True)
    output=ROOT/'data'/f'verification_{args.dps}dps.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
