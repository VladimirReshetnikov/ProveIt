#!/usr/bin/env python3
"""High-precision checks for Uniform q-Multinomial Transseries.

These are numerical consistency checks, not interval-arithmetic proofs.
The analytic error bounds are proved in the accompanying article.
Requires Python >= 3.10 and mpmath >= 1.3.0.
"""
from __future__ import annotations
from functools import lru_cache
from pathlib import Path
import argparse
import json
import math
import mpmath as mp

@lru_cache(maxsize=None)
def eulerian(n: int) -> tuple[int, ...]:
    if n < 1:
        raise ValueError('n must be positive')
    if n == 1:
        return (1,)
    prev = eulerian(n - 1)
    return tuple((k + 1) * (prev[k] if k < len(prev) else 0)
                 + (n - k) * (prev[k - 1] if k else 0) for k in range(n))

def li_negative(p: int, s):
    """Return Li_{-p}(exp(-s)); stable also for very small positive s."""
    s = mp.mpf(s)
    if p < 0 or s <= 0:
        raise ValueError('p >= 0 and s > 0 are required')
    z, d = mp.exp(-s), -mp.expm1(-s)
    if p == 0:
        return z / d
    v = mp.mpf(0)
    for c in reversed(eulerian(p)):
        v = v * z + c
    return z * v / d ** (p + 1)

def parameters(a):
    a = tuple(mp.mpf(t) for t in a)
    if len(a) < 2 or any(t <= 0 for t in a):
        raise ValueError('at least two positive ray parameters are required')
    A = sum(a)
    return a, A, (A*A - sum(t*t for t in a))/2

def neg_log_product(s):
    """-log(prod_{j>=1}(1-exp(-sj))), with s >= 2*pi."""
    s = mp.mpf(s)
    if s < 2 * mp.pi:
        raise ValueError('use the modular transformation when s < 2*pi')
    d = -mp.expm1(-s)
    total = mp.mpf(0)
    for m in range(1, 100000):
        em = mp.exp(-s*m)
        total += em / (m * (1 - em))
        tail = mp.exp(-s*(m+1)) / ((m+1)*d*d)
        if tail < mp.eps / 100:
            return total
    raise ArithmeticError('product summation failed to converge')

def modular_M(h):
    h = mp.mpf(h)
    if h < 0:
        raise ValueError('h must be nonnegative')
    if h == 0:
        return mp.mpf(0)
    dual = 4*mp.pi**2/h
    if dual >= 2*mp.pi:
        return neg_log_product(dual)
    return (neg_log_product(h) + mp.log(2*mp.pi/h)/2
            - mp.pi**2/(6*h) + h/24)

def phase(tau, a):
    a, A, kappa = parameters(a)
    if tau == 0:
        return mp.mpf(0)
    return (kappa*tau*tau + (len(a)-1)*mp.pi**2/6
            + mp.polylog(2, mp.exp(-A*tau))
            - sum(mp.polylog(2, mp.exp(-v*tau)) for v in a))

def log_f(s):
    return mp.log(-mp.expm1(-s)/s) if s else mp.mpf(0)

def core(h, x, a):
    h, x = mp.mpf(h), mp.mpf(x)
    a, A, kappa = parameters(a)
    if h < 0 or x <= 0:
        raise ValueError('h >= 0 and x > 0 are required')
    r, tau = len(a), h*x
    H = A*mp.log(A)-sum(v*mp.log(v) for v in a)
    leading = x*H if h == 0 else phase(tau, a)/h
    amp = (log_f(A*tau)-sum(log_f(v*tau) for v in a))/2
    return (leading - (r-1)*mp.log(2*mp.pi*x)/2
            + mp.log(A/mp.fprod(a))/2 + amp
            - (r-1)*h/24 + (r-1)*modular_M(h))

def coefficient(k, tau, a):
    a, A, _ = parameters(a)
    if k < 1:
        raise ValueError('k must be >= 1')
    if tau == 0:
        return (mp.bernoulli(2*k)/(2*k*(2*k-1))
                * (A**(1-2*k)-sum(v**(1-2*k) for v in a)))
    return (mp.bernoulli(2*k)/mp.factorial(2*k)*tau**(2*k-1)
            * (li_negative(2*k-2, A*tau)
               - sum(li_negative(2*k-2, v*tau) for v in a)))

def truncation(h, x, a=(1, 1), K=3):
    if K < 0:
        raise ValueError('K must be nonnegative')
    h, x = mp.mpf(h), mp.mpf(x)
    return core(h,x,a) + sum(coefficient(k,h*x,a)/x**(2*k-1)
                             for k in range(1,K+1))

def uniform_bound(x, a=(1,1), K=3):
    a, _, _ = parameters(a)
    N = 2*K+1
    return abs(mp.bernoulli(N+1))/(N+1)*sum(v**(-N) for v in a)/mp.mpf(x)**N

def next_term_bound(h,x,a=(1,1),K=3):
    # The strict signed bound is the magnitude of the next correction.
    return abs(coefficient(K+1,mp.mpf(h)*mp.mpf(x),a)/mp.mpf(x)**(2*K+1))

def least_term_K(x,a=(1,1)):
    a, _, _ = parameters(a)
    u=2*mp.pi*min(a)*mp.mpf(x)
    if u < 2*mp.pi:
        raise ValueError('least-term rule requires min(a)*x >= 1')
    # An odd integer within distance one of u. Ties go down.
    lo=2*int(mp.floor((u-1)/2))+1
    N=min((lo,lo+2),key=lambda n:abs(n-u))
    return (N-1)//2

def exponential_bound(x, a=(1,1)):
    """Uniform bound for K selected by least_term_K, proved in the article."""
    a, _, _ = parameters(a)
    z = min(a)*mp.mpf(x)
    if z < 1:
        raise ValueError('the exponential bound requires min(a)*x >= 1')
    return 2*len(a)*mp.exp(-2*mp.pi*z)

def exact_lattice(h,x,a=(1,1)):
    """Independent finite-product evaluation (or the gamma value at h=0)."""
    h,x=mp.mpf(h),mp.mpf(x)
    a,A,kappa=parameters(a)
    if h==0:
        return mp.loggamma(A*x+1)-sum(mp.loggamma(v*x+1) for v in a)
    dims=[v*x for v in a]
    if any(v != mp.floor(v) for v in dims):
        raise ValueError('finite-product reference requires all a_i*x integral')
    def lp(n):
        return sum(mp.log(-mp.expm1(-h*j)) for j in range(1,int(n)+1))
    return kappa*h*x*x+lp(A*x)-sum(lp(v) for v in dims)

def slope_floor(a=(1,1)):
    a,A,_=parameters(a)
    x0=1/min(a)
    return A*mp.digamma(A*x0+1)-sum(v*mp.digamma(v*x0+1) for v in a)

def inverse_certificate(h,L,a=(1,1),K=3,start=5):
    """Return a high-precision approximation and the analytic enclosure formula.

    Printed endpoints are NOT outward rounded; use a validated arithmetic
    backend to turn this routine into a machine-certified interval solver.
    """
    a,A,_=parameters(a)
    c=slope_floor(a)
    s=mp.findroot(lambda x:truncation(h,x,a,K)-L,(mp.mpf(start),mp.mpf(start)+mp.mpf('.01')))
    x0=1/min(a)
    if s<x0:
        raise ValueError('candidate lies below the uniform-slope threshold')
    e=uniform_bound(s,a,K)/c
    return (s,max(x0,s-e),s) if K%2 else (s,s,s+e)

def run(out: Path):
    out.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=240
    rays=[(1,1),(1,2),(1,1,1),(1,3,5)]
    hs=['0','0.00000001','0.001','0.1','0.7','2','10']
    xs=[1,2,5,10,20]
    checked=0
    worst_ratio=mp.mpf(0)
    optimal=[]
    for a in rays:
        for x in xs:
            for ht in hs:
                h=mp.mpf(ht)
                f=exact_lattice(h,x,a)
                ko=least_term_K(x,a)
                Ks=sorted(set([0,1,2,3,5,ko]))
                t=core(h,x,a)
                for k in range(max(Ks)+1):
                    if k:
                        t+=coefficient(k,h*x,a)/mp.mpf(x)**(2*k-1)
                    if k not in Ks:
                        continue
                    rem=f-t
                    signed=(-1)**(k+1)*rem
                    ub=uniform_bound(x,a,k)
                    nb=next_term_bound(h,x,a,k)
                    tol=mp.mpf('1e-190')
                    assert signed>=-tol,(a,x,ht,k,'sign',mp.nstr(rem))
                    assert abs(rem)<=nb+tol,(a,x,ht,k,'next term')
                    assert nb<=ub+tol,(a,x,ht,k,'uniform bound')
                    checked+=1
                    if ub:
                        worst_ratio=max(worst_ratio,abs(rem)/ub)
                    if k==ko:
                        expbd=3*len(a)*mp.sqrt(min(a)*x)*mp.exp(-2*mp.pi*min(a)*x)
                        assert ub<=expbd
                        assert nb<=exponential_bound(x,a)+tol
                        if a==(1,1) and x in [2,5,10,20] and ht in ['0','0.00000001','0.1','2','10']:
                            optimal.append({'h':ht,'x':x,'K':k,'abs_error':mp.nstr(abs(rem),12),
                                            'analytic_bound':mp.nstr(ub,12)})
    sharp=[]
    for a in [(1,1),(1,2),(1,1,1)]:
        for x in [2,5,10,20,40]:
            k=least_term_K(x,a)
            error=abs(exact_lattice(0,x,a)-truncation(0,x,a,k))
            z=min(a)*mp.mpf(x)
            multiplicity=sum(v==min(a) for v in a)
            prediction=multiplicity/(2*mp.pi*mp.sqrt(z))*mp.exp(-2*mp.pi*z)
            sharp.append({'ray':list(a),'x':x,'K':k,'ratio_to_sharp_equivalent':mp.nstr(error/prediction,14)})
    inverse=[]
    for a in [(1,1),(1,2),(1,1,1)]:
        for ht in ['0','0.0001','0.2','2']:
            for x in [5,10]:
                h=mp.mpf(ht)
                L=exact_lattice(h,x,a)
                k=3
                s,lo,hi=inverse_certificate(h,L,a,k,x)
                tol=mp.mpf('1e-185')
                assert lo-tol<=x<=hi+tol
                inverse.append({'ray':list(a),'h':ht,'true_x':x,'K':k,
                                's_minus_x':mp.nstr(s-x,12),'width':mp.nstr(hi-lo,12)})
    # Elementary sum bound and the exact first coefficients at the endpoint.
    for p in range(0,15):
        for s in ['0.0001','.2','1','3','10']:
            v=mp.mpf(s)
            assert v**(p+1)*li_negative(p,v)<=mp.factorial(p+1)*(1+mp.mpf('1e-200'))
    expected=[mp.mpf(-1)/8,mp.mpf(1)/192,-mp.mpf(1)/640,mp.mpf(17)/14336]
    for k,v in enumerate(expected,1):
        assert abs(coefficient(k,0,(1,1))-v)<mp.mpf('1e-220')
    resonant=[]
    for a in [(1,1),(1,2),(1,1,1)]:
        multiplicity=sum(v==min(a) for v in a)
        for m0 in [1,2,3]:
            h=2*mp.pi/m0
            for x in [5,10,20,40]:
                k=least_term_K(x,a)
                error=abs(exact_lattice(h,x,a)-truncation(h,x,a,k))
                prediction=multiplicity/(2*mp.pi*m0)*mp.exp(-2*mp.pi*min(a)*x)
                assert error<=exponential_bound(x,a)
                resonant.append({'ray':list(a),'m0':m0,'x':x,'K':k,
                                 'ratio_to_resonant_equivalent':mp.nstr(error/prediction,14)})
    peak_checks=0
    for N in [5,7,11,21,51,101]:
        for value in [mp.mpf('.001'),mp.mpf('.5'),mp.mpf(1),N/2,mp.mpf(N),mp.mpf(N+1),2*N,10*N]:
            s=mp.mpf(value)
            assert s**N*li_negative(N-1,s)<=3*mp.power(N,N)*mp.exp(-N)
            peak_checks+=1
    report={'precision_decimal_digits':mp.mp.dps,'forward_inequality_checks':checked,
            'inverse_checks':len(inverse),'resonance_checks':len(resonant),
            'peak_moment_checks':peak_checks,'worst_error_over_uniform_bound':mp.nstr(worst_ratio,14),
            'status':'All checks passed; high-precision numerical checks, not interval proofs.',
            'optimal_examples':optimal,'sharpness_examples':sharp,'inverse_examples':inverse,'resonance_examples':resonant}
    (out/'verification_results.json').write_text(json.dumps(report,indent=2)+'\n')
    table=['\\begin{tabular}{rrrrr}','\\toprule','$h$ & $x$ & $K$ & $|F-T_K|$ & $E_K(x)$ \\\\','\\midrule']
    def texnum(s):
        v=mp.mpf(s)
        if not v:return '0'
        e=int(mp.floor(mp.log10(v)))
        return mp.nstr(v/mp.power(10,e),5)+r'\times10^{'+str(e)+'}'
    chosen=[v for v in optimal if (v['x']==5 and v['h'] in ['0','0.00000001','0.1','2','10'])
            or (v['h']=='0.1' and v['x'] in [2,10,20])]
    for v in chosen:
        table.append(f"{v['h']} & {v['x']} & {v['K']} & ${texnum(v['abs_error'])}$ & ${texnum(v['analytic_bound'])}$ \\\\")
    table+=['\\bottomrule','\\end{tabular}']
    (out/'numerical_table.tex').write_text('\n'.join(table)+'\n')
    print(json.dumps({k:v for k,v in report.items() if not isinstance(v,list)},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).parent)
    args=parser.parse_args()
    run(args.out)
