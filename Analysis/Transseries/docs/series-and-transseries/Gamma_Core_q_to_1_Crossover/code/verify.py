#!/usr/bin/env python3
"""Audits for Gamma-core Gaussian-binomial transseries.
Run python code/verify.py [--quick]. Needs mpmath, sympy.
Floating-point checks are NOT outward-rounded interval certificates.
"""
from __future__ import annotations
import argparse, json, platform
from pathlib import Path
import mpmath as mp
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]

def core_log(x):
    x=mp.mpf(x)
    if x<0: raise ValueError('x >= 0 required')
    return mp.loggamma(2*x+1)-2*mp.loggamma(x+1)

def exact_log(h,x):
    """Positive Lambert sum and explicit omitted-tail bound."""
    h,x=mp.mpf(h),mp.mpf(x)
    if h<=0 or x<0: raise ValueError('h>0, x>=0 required')
    if not x: return mp.mpf(0),mp.mpf(0)
    n=max(1,int(mp.ceil((mp.mp.dps+12)*mp.log(10)/h)))
    value=h*x*x+mp.fsum(mp.expm1(-h*m*x)**2/(m*mp.expm1(h*m)) for m in range(1,n+1))
    tail=mp.exp(-h*(n+1))/((n+1)*(1-mp.exp(-h))*(1-mp.exp(-h*(n+1))))
    return value,tail

def finite_log(h,n):
    h=mp.mpf(h)
    if n<0 or int(n)!=n: raise ValueError('nonnegative integer n required')
    return mp.fsum(mp.log(mp.expm1(h*(n+j)))-mp.log(mp.expm1(h*j)) for j in range(1,int(n)+1))

def f_derivative(t,r):
    """Derivatives via conjugate Hurwitz-zeta pole sums."""
    t=mp.mpf(t)
    if r<1 or t<0: raise ValueError('r>=1, t>=0 required')
    if r==1:
        return mp.mpf('.5') if not t else mp.mpf('.5')+mp.coth(t/2)/2-1/t
    if not t and r%2: return mp.mpf(0)
    a=2*mp.pi
    term=(1j*a)**(-r)*mp.zeta(r,1-1j*t/a)
    return (-1)**(r-1)*mp.factorial(r-1)*2*mp.re(term)

def phase_A(t):
    t=mp.mpf(t)
    if not t: return mp.mpf(0)
    if t<mp.mpf('.1'):
        return t*t/2+2*mp.quad(lambda s:mp.log(mp.cosh(s/2)),[0,t])
    z=mp.exp(-t)
    return t*t+mp.pi**2/6+mp.polylog(2,z*z)-2*mp.polylog(2,z)-2*t*mp.log(2)

def amplitude_B(t):
    t=mp.mpf(t)
    return mp.mpf(0) if not t else mp.log((t/2)*mp.coth(t/2))/2

def regular_coefficient(t,k):
    r=2*k-1
    return mp.bernoulli(2*k)/mp.factorial(2*k)*(f_derivative(2*t,r)-2*f_derivative(t,r)+f_derivative(0,r))

def composite_log(h,x,K):
    h,x=mp.mpf(h),mp.mpf(x)
    if h<=0 or x<0 or K<1: raise ValueError('h>0, x>=0, K>=1 required')
    if not x: return mp.mpf(0)
    t=h*x
    return core_log(x)+phase_A(t)/h+amplitude_B(t)+mp.fsum(h**(2*k-1)*regular_coefficient(t,k) for k in range(1,K+1))

def d_bound(r):
    if r==2: return mp.mpf('.5')
    return mp.factorial(r-1)*mp.sqrt(mp.pi)*mp.gamma(mp.mpf(r-1)/2)/mp.gamma(mp.mpf(r)/2)*mp.zeta(r-1)/(2*mp.pi)**(r-1)

def error_bounds(h,K):
    h=mp.mpf(h);p=2*mp.zeta(2*K)/(2*mp.pi)**(2*K)
    eps=4*p*h**(2*K-1)*d_bound(2*K)
    eta=max(3*p*h**(2*K+1)*d_bound(2*K+2),6*p*h**(2*K)*d_bound(2*K+1))
    inv=max(eta/(1-eta),2*eps) if eta<1 else mp.inf
    return eps,eta,inv

def optimal_K(h): return max(2,int(mp.ceil(2*mp.pi**2/mp.mpf(h))))

def modular_M(h):
    h=mp.mpf(h);r=mp.exp(-4*mp.pi**2/h)
    n=max(2,int(mp.ceil((mp.mp.dps+12)*mp.log(10)*h/(4*mp.pi**2))))
    return mp.fsum(r**m/(m*(1-r**m)) for m in range(1,n+1))

def half_analytic_log(h):
    h=mp.mpf(h)
    return mp.log(4/mp.pi)+h/8+mp.log((h/4)*mp.coth(h/4))

def rational_coefficient(x,m):
    return sp.bernoulli(2*m)/(2*m*sp.factorial(2*m+1))*(sp.bernoulli(2*m+1,2*x+1)-2*sp.bernoulli(2*m+1,x+1))

def fmt(v): return mp.nstr(v,35)

def main():
    p=argparse.ArgumentParser();p.add_argument('--quick',action='store_true');args=p.parse_args()
    mp.mp.dps=100 if args.quick else 190
    out={'precision_digits':mp.mp.dps,'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,'interval_arithmetic':False,'tests':{},'forward':[],'bounds':[],'half_integer':[],'large_order':[],'inverse':[]}
    x=sp.Symbol('x');polys=[sp.factor(rational_coefficient(x,m)) for m in range(1,6)]
    out['exact_polynomials']=[str(v) for v in polys]
    for n in range(1,8):
        for m in range(1,7):
            rhs=sp.bernoulli(2*m)/(2*m*sp.factorial(2*m))*(sum(j**(2*m) for j in range(1,2*n+1))-2*sum(j**(2*m) for j in range(1,n+1)))
            assert sp.expand(rational_coefficient(sp.Integer(n),m)-rhs)==0
    assert sp.expand(polys[0]-x*x*(2*x+1)/24)==0
    out['tests']['exact_faulhaber_checks']=42
    for hs in (['1','0.5'] if args.quick else ['1','0.5','0.25']):
        h=mp.mpf(hs);K=optimal_K(h);eps,eta,inv=error_bounds(h,K);scale=mp.exp(-4*mp.pi**2/h)
        out['bounds'].append({'h':hs,'K':K,'epsilon':fmt(eps),'eta':fmt(eta),'inverse_bound':fmt(inv),'epsilon_over_scale':fmt(eps/scale),'eta_over_scale':fmt(eta/scale)})
        for ts in (['0.05','1','10'] if args.quick else ['0.001','0.05','0.5','1','5','20']):
            t=mp.mpf(ts);xx=t/h;value,tail=exact_log(h,xx);appr=composite_log(h,xx,K);err=abs(value-appr)
            assert err+tail<eps,(hs,ts,fmt(err/eps))
            assert core_log(xx)+h*xx*xx/2<=value+tail
            assert value<=core_log(xx)+h*xx*xx+tail
            out['forward'].append({'h':hs,'tau':ts,'x':fmt(xx),'K':K,'absolute_error':fmt(err),'error_over_scale':fmt(err/scale),'error_over_bound':fmt(err/eps),'omitted_tail_bound':fmt(tail)})
        value,tail=exact_log(h,mp.mpf('.5'));defect=value-half_analytic_log(h);pred=4*modular_M(h)-2*modular_M(h/2)
        assert abs(defect-pred)<mp.mpf(10)**(-mp.mp.dps+10)
        out['half_integer'].append({'h':hs,'defect':fmt(defect),'predicted_defect':fmt(pred),'defect_over_scale':fmt(defect/scale)})
    for n in [1,2,5]:
        value,tail=exact_log(1,n);assert abs(value-finite_log(1,n))<mp.mpf(10)**(-mp.mp.dps+10)
    out['tests']['finite_product_agreement']=3
    A=4*mp.pi**2;amplitude=mp.sin(4*mp.pi/3)-2*mp.sin(2*mp.pi/3)
    for m in [5,10,20,40,80]:
        actual=mp.mpf(str(sp.N(rational_coefficient(sp.Rational(1,3),m),mp.mp.dps+5)))
        pred=2/mp.pi*amplitude*mp.factorial(2*m-1)/A**(2*m)
        out['large_order'].append({'x':'1/3','m':m,'ratio':fmt(actual/pred)})
    for xs in (['0.1','2'] if args.quick else ['0.01','0.1','2','20']):
        h=mp.mpf(1);xx=mp.mpf(xs);K=optimal_K(h);target,_=exact_log(h,xx)
        root=mp.findroot(lambda u:composite_log(h,u,K)-target,(xx*mp.mpf('.99'),xx*mp.mpf('1.01')),solver='secant',tol=mp.mpf(10)**(-mp.mp.dps+15),maxsteps=20)
        eps,eta,bound=error_bounds(h,K);assert abs(root-xx)<bound
        out['inverse'].append({'h':'1','target_root':xs,'approximate_root':fmt(root),'absolute_error':fmt(abs(root-xx)),'bound':fmt(bound)})
    out['tests']['all_passed']=True
    path=ROOT/'data'/('verification_quick.json' if args.quick else 'verification.json')
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__': main()
