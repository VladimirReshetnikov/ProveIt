#!/usr/bin/env python3
"""Independent marked-jet and polynomial-weight diagnostics.

A convergent small-mass expansion is integrated numerically for the beta
identities. Its coefficients are obtained by differentiating (m+w)_k,
not from the finite collision formula being tested. All numeric results
are diagnostics, not rigorous error enclosures or proof-assistant checks.
"""
from __future__ import annotations
import json, math, time, platform
from pathlib import Path
from functools import lru_cache
import mpmath as mp
import sympy as sp
import verify as base

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
exact=[]; numerical=[]

def check_exact(name, value):
    assert sp.simplify(value)==0,(name,value)
    exact.append(name)

def check_num(name, left, right, tol='1e-41'):
    err=abs(left-right); rel=err/max(mp.mpf(1),abs(left),abs(right))
    passed=rel<mp.mpf(tol)
    numerical.append(dict(name=name,left=str(mp.nstr(left,58)),right=str(mp.nstr(right,58)),
         absolute_residual=mp.nstr(err,9),relative_residual=mp.nstr(rel,9),tolerance=tol,passed=passed))
    assert passed,(name,mp.nstr(err,10))

@lru_cache(None)
def jcoeff(m,N,astr,K=85):
    """Power series of J_{m,N}(a,t) at t=0, independent infinite route."""
    a=mp.mpf(astr)
    out=[mp.stieltjes(N,a)]
    # Taylor coefficients of (m+w)_k/k!: update directly by multiplication.
    p=[mp.mpf(1)]+[mp.mpf(0)]*N
    for k in range(1,K+1):
        old=p[:]
        p=[((m+k-1)*old[r]+(old[r-1] if r else 0))/k for r in range(N+1)]
        val=mp.mpf(0)
        for r in range(N+1):
            z=base.zd(N-r,k+1,astr)
            val+=math.comb(N,r)*math.factorial(r)*p[r]*z
        out.append((-1)**(N+k)*val)
    return tuple(out)

def jseries(m,N,a,u):
    return mp.polyval(list(reversed(jcoeff(m,N,str(a)))),mp.mpf(u))

def complete_h(m,r):
    co=[sp.S.One]+[sp.S.Zero]*r
    for j in range(1,m):
        for k in range(1,r+1):
            co[k]+=co[k-1]/sp.Integer(j)
    return co[r]

def run():
    start=time.time(); s,z=sp.symbols('s z')
    from sympy.functions.combinatorial.numbers import stirling
    # Residue obtained by separately expanding all equal-mass spectra versus
    # coefficient extraction from the complete logarithmic product.
    for m in range(1,7):
        for k in range(m,m+6):
            poly=sp.Poly(sp.expand(sum((-1)**(m-j)*sp.binomial(m,j)*sp.rf(j*s,k)/sp.factorial(k)
                                  for j in range(m+1))),s)
            c=poly.coeff_monomial(s**m)
            target=sp.factorial(m)*stirling(k,m,kind=1)/sp.factorial(k)
            check_exact(f'weight_residue_m{m}_k{k}',c-target)
    # Inverse Gamma ratio derivatives use complete homogeneous harmonics.
    for m in range(2,8):
        inv=sp.series(sp.prod(1/(1+s/sp.Integer(j)) for j in range(1,m)),s,0,6).removeO()
        for r in range(6):
            check_exact(f'inverse_gamma_harmonic_m{m}_r{r}',sp.expand(inv).coeff(s,r)-(-1)**r*complete_h(m,r))
    # Spectral collision formula compared to a different infinite Taylor sum.
    a=mp.mpf('1.2');u=mp.mpf('0.18')
    for m,N in [(2,1),(2,2),(3,1),(3,2),(4,2)]:
        check_num(f'marked_collision_m{m}_N{N}',jseries(m,N,a,u),base.J(m,N,a,u))
    # Ordinary quadrature of independently constructed marked collision jets.
    # This avoids repeatedly estimating Stieltjes constants inside quadrature.
    for m,N in [(2,1),(2,2),(3,1),(3,2),(4,2)]:
        polys=[list(reversed(jcoeff(m,k,str(a)))) for k in range(N+1)]
        def integrand(y):
            return (1-y)**(m-2)*sum(math.comb(N,k)*(-mp.log(y))**(N-k)*
                         mp.polyval(polys[k],u*y) for k in range(N+1))
        left=mp.quad(integrand,[0,mp.mpf('.5'),1])
        right=sum(math.comb(N,k)*math.factorial(N-k)*base.mpq(complete_h(m,N-k))*
                  mp.stieltjes(k,a+u) for k in range(N+1))/(m-1)
        check_num(f'marked_beta_primitive_m{m}_N{N}',left,right)
    # First regular connected derivative: individual spectral continuations,
    # followed only then by inclusion-exclusion. Independent Gamma quadrature.
    for m in [2,3]:
        uu=mp.mpf('0.12')
        vals=[base.partial_equal_spectrum_jet(m,j,m,a,uu) for j in range(m+1)]
        left=sum((-1)**(m-j)*math.comb(m,j)*vals[j] for j in range(m+1))
        right=(-1)**m*mp.factorial(m)*base.F0_integral(a,[uu]*m)
        check_num(f'first_regular_connected_derivative_m{m}',left,right)
    # Finite Gamma-normalized differential operator off w=0 (complex parameter).
    w=mp.mpc('0.17','0.09')
    for m in [2,3,4]:
        left=sum(math.comb(m-1,r)*(-u)**r*mp.zeta(1+w+r,a+u) for r in range(m))-1/w
        right=mp.gamma(1+w)/mp.gamma(m+w)*u**(-w)*mp.diff(
             lambda v:v**(m-1+w)*(mp.zeta(1+w,a+v)-1/w),u,m-1)
        check_num(f'gamma_differential_operator_m{m}',left,right)
    # Marked polylogarithmic generators from direct n series vs order derivatives.
    for alpha,us0 in [((1,0),('0.15','0.21')),((1,1),('0.15','0.21')),((2,0,0),('0.1','0.17','0.22'))]:
        us=list(map(mp.mpf,us0));m=len(us);zz=mp.mpf('.38')
        direct=sum(n**(m-1)*zz**n*mp.fprod(base.qlog(r,mp.mpf(n),u) for r,u in zip(alpha,us))
                   for n in range(1,230))
        co=base.log_coefficients(alpha,us,70)
        poly=mp.mpf(0)
        for (k,l),c in co.items():
            lv=mp.polylog(k-m+1,zz) if l==0 else mp.diff(lambda v:mp.polylog(v,zz),mp.mpf(k-m+1),l)
            poly+=c*(-1)**l*lv
        check_num('marked_polylog_'+str(alpha),direct,poly,'1e-39')
    data=dict(status='passed',exact_assertions=len(exact),numerical_diagnostics=len(numerical),
       working_decimal_digits=mp.mp.dps,interval_certified=False,proof_assistant_formalization=False,
       python=platform.python_version(),sympy=sp.__version__,mpmath=mp.__version__,
       elapsed_seconds=round(time.time()-start,3),exact_checks=exact,numerical_checks=numerical)
    (ROOT/'results'/'supplemental-validation.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ['exact_checks','numerical_checks']},indent=2))
    return data
if __name__=='__main__':run()
