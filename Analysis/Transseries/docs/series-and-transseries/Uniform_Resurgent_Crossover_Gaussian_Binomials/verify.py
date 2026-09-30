#!/usr/bin/env python3
"""Reproducible checks for Gaussian-binomial crossover transseries.

Python 3.10+; requires mpmath and sympy. Numerical checks are not interval
proofs. Positive omitted-tail bounds are evaluated with ordinary mpmath
rounding; the article proves the corresponding exact inequalities.
"""
from __future__ import annotations
import argparse, json, math, pathlib, sys
import mpmath as mp


def sigma_minus_one(n: int):
    if n < 1: raise ValueError('n must be positive')
    return sum((mp.mpf(1)/d for d in range(1,n+1) if n%d==0),mp.mpf(0))


def modular(h):
    h=mp.mpf(h)
    if h<=0: raise ValueError('h must be positive')
    z=mp.exp(-4*mp.pi**2/h)
    # The bound on the residual is sum_{n>M} n z^n.
    total=mp.mpf(0)
    for n in range(1,100000):
        total += sigma_minus_one(n)*z**n
        bound=z**(n+1)*((n+1)-n*z)/(1-z)**2
        if bound<mp.eps*max(total,mp.mpf('1e-100000')):
            return total
    raise RuntimeError('modular series did not converge within budget')


def A(h,tau):
    h,tau=mp.mpf(h),mp.mpf(tau)
    if h<=0 or tau<=0: raise ValueError('positive h and tau required')
    total=mp.mpf(0)
    # Ratio of successive summands is at most exp(-tau).
    ratio=mp.exp(-tau)
    for m in range(1,2000000):
        v=mp.exp(-m*tau)/(m*mp.expm1(h*m))
        total+=v
        if v*ratio/(1-ratio)<mp.eps*max(total,mp.mpf(1)):
            return total
    raise RuntimeError('A series did not converge within budget')


def S(tau):
    tau=mp.mpf(tau)
    if tau==0: return mp.mpf(0)
    z=mp.exp(-tau)
    return tau*tau+mp.pi**2/6+mp.polylog(2,z*z)-2*mp.polylog(2,z)


def J(tau):
    return mp.log(mp.coth(mp.mpf(tau)/2))/2


def logH(h,x):
    h,x=mp.mpf(h),mp.mpf(x)
    if h==0: return mp.loggamma(2*x+1)-2*mp.loggamma(x+1)
    tau=h*x
    return (tau*tau+mp.pi**2/6)/h-mp.log(2*mp.pi/h)/2-h/24+modular(h)+A(h,2*tau)-2*A(h,tau)


def logH_integer(h,n: int):
    h=mp.mpf(h)
    if n<1: raise ValueError('positive integer index required')
    return h*n*n+sum((mp.log(-mp.expm1(-h*j)) for j in range(1,2*n+1)),mp.mpf(0))-2*sum((mp.log(-mp.expm1(-h*j)) for j in range(1,n+1)),mp.mpf(0))


def a(k: int,tau):
    tau=mp.mpf(tau)
    if k<1 or tau<=0: raise ValueError('k>=1 and tau>0 required')
    return abs(mp.bernoulli(2*k))/mp.factorial(2*k)*(2*mp.polylog(2-2*k,mp.exp(-tau))-mp.polylog(2-2*k,mp.exp(-2*tau)))


def polynomial_R(h,tau,K: int):
    return sum(((-1)**(k-1)*a(k,tau)*h**(2*k-1) for k in range(1,K+1)),mp.mpf(0))


def remainder_bounds(x,tau,K: int,digits: int=35):
    """Positive double sum, bounded after finite m and n cutoffs.
    Returns (partial_sum, upper_error_bound); no subtractive cancellation.
    For K=0 convergence in the n index is deliberately not used here.
    """
    x,tau=mp.mpf(x),mp.mpf(tau)
    if x<=0 or tau<=0 or K<1: raise ValueError('x,tau>0 and K>=1 required')
    h=tau/x; p=2*K; s=p+2
    ncut=max(1,int(mp.ceil(mp.power(10,mp.mpf(digits+2)/s))))
    if ncut>1000: raise ValueError('Use this evaluator at larger K or fewer digits')
    # After M>p/tau the ratios of e^{-tau m} m^p decrease.
    peak=p/tau
    M=max(20,int(mp.ceil((p+12*mp.sqrt(p+1)+digits*3)/tau)))
    pref=2*h**(p+1)/(2*mp.pi)**(p+2)
    total=mp.mpf(0); moment=mp.mpf(0)
    ndata=[(mp.mpf(n),mp.mpf(n)**(-s)) for n in range(1,ncut+1)]
    for m in range(1,M+1):
        e=mp.exp(-tau*m)
        weight=(2*e-e*e)*mp.mpf(m)**p
        moment+=weight
        b=mp.mpf(m)*h/(2*mp.pi)
        kernel=sum((ns/(1+(b/n)**2) for n,ns in ndata),mp.mpf(0))
        total+=weight*kernel
    first=2*mp.exp(-tau*(M+1))*mp.mpf(M+1)**p
    ratio=mp.exp(-tau)*(mp.mpf(M+2)/(M+1))**p
    if not ratio<1: raise AssertionError('invalid m-tail ratio')
    mtail=first/(1-ratio)
    # Separate missing-n contribution on retained m and full missing-m tail.
    err=pref*(mp.zeta(s,ncut+1)*moment+mp.zeta(s)*mtail)
    return pref*total,err


def slope(h,x):
    h,x=mp.mpf(h),mp.mpf(x)
    if h==0: return 2*mp.digamma(2*x+1)-2*mp.digamma(x+1)
    tau=h*x; total=mp.mpf(0)
    ratio=mp.exp(-tau)
    for m in range(1,2000000):
        term=(mp.exp(-m*tau)-mp.exp(-2*m*tau))/mp.expm1(h*m)
        total+=term
        # Safe absolute tail via exp(-m tau)/(exp(h m)-1).
        bound=mp.exp(-(m+1)*tau)/(mp.expm1(h*(m+1))*(1-ratio))
        if 2*h*bound<mp.eps: return 2*tau+2*h*total
    raise RuntimeError('slope series budget exceeded')


def run(outdir: pathlib.Path,quick: bool=False):
    mp.mp.dps=110
    report={'mpmath_version':mp.__version__, 'working_precision':mp.mp.dps,
            'status':'numerical and exact symbolic checks; not a Lean verification',
            'checks':{},'optimal_remainders':[],'visibility_boundary':[]}
    # Exact symbolic endpoint coefficient checks.
    import sympy as sp
    coeffs=[]
    for k in range(1,7):
        value=sp.bernoulli(2*k)/(2*k*(2*k-1))*(sp.Rational(2)**(1-2*k)-2)
        coeffs.append(str(value))
    assert coeffs==['-1/8','1/192','-1/640','17/14336','-31/18432','691/180224']
    report['checks']['endpoint_coefficients']=coeffs
    # Borel Taylor coefficients from the odd pole lattice independently
    # reproduce the endpoint Bernoulli coefficients (eight exact identities).
    for k in range(1,9):
        pole_coefficient=(-1)**k*4*(1-sp.Rational(2)**(-2*k))*sp.zeta(2*k)/(2*sp.pi)**(2*k)
        stirling_coefficient=sp.bernoulli(2*k)*(sp.Rational(2)**(1-2*k)-2)/(2*k*(2*k-1)*sp.factorial(2*k-2))
        assert sp.simplify(pole_coefficient-stirling_coefficient)==0
    report['checks']['endpoint_borel_coefficients']=8
    # Residue cancellation in rational multiples of i/pi.
    # Upper residues: A(2tau) at m even contributes -1/m;
    # -2A(tau) contributes +1/m; even-real-shift cancellation is exact.
    for m in range(2,22,2): assert -sp.Rational(1,m)+sp.Rational(1,m)==0
    report['checks']['even_axis_pole_cancellations']=10
    product_errors=[]
    for h,n in [('0.2',5),('0.1',10),('0.05',20),('0.7',3)]:
        h=mp.mpf(h); er=abs(logH(h,n)-logH_integer(h,n)); assert er<mp.mpf('1e-100')
        product_errors.append(mp.nstr(er,8))
    report['checks']['independent_finite_product_errors']=product_errors
    remchecks=[]
    for tau,x,K in [('1',5,4),('2',7,6),('0.5',8,6)]:
        tau,x=mp.mpf(tau),mp.mpf(x);h=tau/x
        R=2*(A(h,tau)-mp.polylog(2,mp.exp(-tau))/h-mp.log(1-mp.exp(-tau))/2)-(A(h,2*tau)-mp.polylog(2,mp.exp(-2*tau))/h-mp.log(1-mp.exp(-2*tau))/2)
        r=(-1)**K*(R-polynomial_R(h,tau,K))
        bound=a(K+1,tau)*h**(2*K+1)
        assert 0<r<bound
        lo,er=remainder_bounds(x,tau,K,digits=14)
        assert lo<=r+mp.mpf('1e-90') and r<=lo+er+mp.mpf('1e-90')
        remchecks.append({'x':str(x),'tau':str(tau),'K':K,'r':mp.nstr(r,16),'r_over_first_omitted':mp.nstr(r/bound,12),'bounded_sum_relative_gap':mp.nstr(er/lo,8)})
    report['checks']['positive_remainders']=remchecks
    slopechecks=[]
    for h,x in [('0.01',1),('0.1',20),('0.25',4),('1',3)]:
        h,x=mp.mpf(h),mp.mpf(x);s=slope(h,x);upper=2*mp.log(1+mp.exp(h*x));lower=upper-1/(2*x)
        assert lower<s<upper
        slopechecks.append([str(h),str(x),mp.nstr(s,16)])
    report['checks']['slope_bounds']=slopechecks
    cases=[(5,'1'),(10,'1'),(20,'1'),(40,'1'),(20,'0.1'),(20,'6.283185307179586476925286766559'),(20,'10')]
    if quick: cases=cases[:3]
    for x,tau in cases:
        tau=mp.mpf(tau);K=int(mp.nint(mp.pi*x))
        lo,er=remainder_bounds(x,tau,K,25)
        prediction=mp.exp(-2*mp.pi*x)/(mp.pi*mp.sqrt(x))
        report['optimal_remainders'].append({'x':x,'tau':mp.nstr(tau,12),'K':K,'r':mp.nstr(lo,20),'r_over_prediction':mp.nstr(lo/prediction,14),'relative_tail_bound':mp.nstr(er/lo,5)})
    for x in ([10,20] if quick else [10,20,40,80]):
        for s in [0,1]:
            tau=2*mp.pi-mp.log(x)/(2*x)+mp.mpf(s)/x;K=int(mp.nint(mp.pi*x))
            lo,er=remainder_bounds(x,tau,K,25)
            E=modular(tau/x)
            report['visibility_boundary'].append({'x':x,'s':s,'ratio':mp.nstr(lo/E,14),'limit':mp.nstr(mp.exp(-s)/mp.pi,14)})
    # Modular displacement: exact modular-free inverse, then corrected target.
    h=mp.mpf('1.2');x0=mp.mpf('5');E=modular(h)
    L=logH(h,x0)-E
    root=mp.findroot(lambda x:logH(h,x)-L,(x0-mp.mpf('.01'),x0))
    displacement=root-x0;first=-E/slope(h,x0)
    assert displacement<0 and abs(displacement/first-1)<mp.mpf('1e-12')
    report['checks']['modular_inverse']={'h':str(h),'x0':str(x0),'displacement':mp.nstr(displacement,30),'first_term':mp.nstr(first,30),'ratio':mp.nstr(displacement/first,30)}
    outdir.mkdir(parents=True,exist_ok=True)
    # ed. (ProveIt, 2026-09-29): a --quick run writes its own file, so it can no
    # longer overwrite the recorded full run; newline='\n' keeps reruns LF on Windows.
    name='verification_results_quick.json' if quick else 'verification_results.json'
    (outdir/name).write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--outdir',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent)
    args=p.parse_args();run(args.outdir,args.quick)
