#!/usr/bin/env python3
"""Reproduce the paper's finite algebra and numerical checks.

Requires Python >=3.10, mpmath 1.3.0, sympy 1.14.0.
Floating-point results are NOT outward-rounded interval certificates.
The remainder tail formulas used below are proved in the paper.
Run: python verification/verify.py (writes verification/results.json).
"""
from __future__ import annotations
import json
import platform
from pathlib import Path
import mpmath as mp
import sympy as sp


def text(x, digits=24):
    return mp.nstr(x, digits)


def moment_data(h, x, M: int, blocks=(1, 1)):
    if h <= 0 or x <= 0 or M < 0:
        raise ValueError('Require h>0, x>0 and M>=0.')
    tau=h*x; lam=min(blocks)*tau; total=sum(blocks)
    p=2*M
    N=int(mp.ceil((mp.mp.dps*mp.log(10)+p*mp.log(p+2)+70)/lam))
    N=max(N, int(mp.ceil(p/lam))+1)
    vals=[]; zs=[]; dx=[]
    for m in range(1,N+1):
        es=[mp.exp(-a*tau*m) for a in blocks]
        end=mp.exp(-total*tau*m)
        vals.append(mp.fsum(es)-end)
        dx.append(h*m*(-mp.fsum(a*e for a,e in zip(blocks,es))+total*end))
        zs.append((h*m/(2*mp.pi))**2)
    terms=[]; deriv=[]
    for j in range(M+1):
        c=h*mp.zeta(2*j+2)/(2*mp.pi**2)
        terms.append(c*mp.fsum(vals)); deriv.append(c*mp.fsum(dx))
        if j<M:
            vals=[v*z for v,z in zip(vals,zs)]
            dx=[v*z for v,z in zip(dx,zs)]
    tail=(h/(2*mp.pi**2)*mp.zeta(p+2)*(h/(2*mp.pi))**p
          *len(blocks)*mp.gammainc(p+1,lam*N,mp.inf)/lam**(p+1))
    return terms,deriv,vals,zs,tail,N


def positive_remainder(h,x,M: int,blocks=(1,1)):
    terms,deriv,vals,zs,mtail,N=moment_data(h,x,M,blocks)
    p=2*M
    K=min(20,max(6,int(mp.ceil(mp.power(10,mp.mpf(20)/(p+1))))))
    value=h/(2*mp.pi**2)*mp.fsum(
        mp.fsum(v/(1+z/(k*k)) for v,z in zip(vals,zs))/mp.mpf(k)**(p+2)
        for k in range(1,K+1))
    # Integral test for sum_{k>K} k^{-p-2}.
    ktail=h/(2*mp.pi**2)*mp.fsum(vals)/(mp.mpf(p+1)*mp.mpf(K)**(p+1))
    return value,mtail+ktail,terms[-1],terms,deriv


def phase(tau, blocks=(1,1)):
    A=sum(blocks); c=(A*A-sum(a*a for a in blocks))/2
    return (c*tau*tau+(len(blocks)-1)*mp.pi**2/6
            +mp.polylog(2,mp.exp(-A*tau))
            -mp.fsum(mp.polylog(2,mp.exp(-a*tau)) for a in blocks))


def phase_slope(tau,blocks=(1,1)):
    A=sum(blocks)
    return mp.fsum(a*mp.log(mp.expm1(A*tau)/mp.expm1(a*tau)) for a in blocks)


def base(h,x,blocks=(1,1)):
    tau=h*x; A=sum(blocks); d=len(blocks)
    amp=((d-1)*mp.log(h/(2*mp.pi))+mp.log(-mp.expm1(-A*tau))
         -mp.fsum(mp.log(-mp.expm1(-a*tau)) for a in blocks))/2
    return phase(tau,blocks)/h+amp-(d-1)*h/24


def modular(h):
    r=mp.exp(-4*mp.pi**2/h)
    N=max(3,int(mp.ceil((mp.mp.dps+10)*mp.log(10)/(-mp.log(r)))))
    return -mp.fsum(mp.log1p(-r**k) for k in range(1,N+1))


def exact_log(h,x,blocks=(1,1)):
    tau=h*x; lam=min(blocks)*tau; A=sum(blocks)
    N=int(mp.ceil((mp.mp.dps+15)*mp.log(10)/lam))+2
    # Direct thermal series, independent of Bernoulli truncation.
    F=-mp.fsum((mp.fsum(mp.exp(-a*tau*m) for a in blocks)-mp.exp(-A*tau*m))/m
       *(1/mp.expm1(h*m)-1/(h*m)+mp.mpf('.5')) for m in range(1,N+1))
    return base(h,x,blocks)+(len(blocks)-1)*modular(h)+F


def truncation(h,x,M,blocks=(1,1),with_slope=False):
    terms,ders,*_=moment_data(h,x,M,blocks)
    val=base(h,x,blocks)+mp.fsum((-1)**(j+1)*terms[j] for j in range(M))
    if not with_slope:
        return val
    tau=h*x;A=sum(blocks)
    amp_der=h/2*(A/mp.expm1(A*tau)-mp.fsum(a/mp.expm1(a*tau) for a in blocks))
    slope=phase_slope(tau,blocks)+amp_der+mp.fsum((-1)**(j+1)*ders[j] for j in range(M))
    return val,slope


def pade_value(coeff,L,N,s):
    mat=sp.Matrix([[coeff[k-j] if k-j>=0 else 0 for j in range(1,N+1)]
                   for k in range(L+1,L+N+1)])
    rhs=sp.Matrix([-coeff[k] for k in range(L+1,L+N+1)])
    qs=[sp.S.One]+list(mat.inv()*rhs)
    ps=[sum(qs[j]*coeff[k-j] for j in range(min(k,N)+1)) for k in range(L+1)]
    return sp.cancel(sum(p*s**k for k,p in enumerate(ps))/sum(q*s**k for k,q in enumerate(qs)))


def run():
    report={'environment':{'python':platform.python_version(),'mpmath':mp.__version__,
                           'sympy':sp.__version__},
            'status':'Floating-point checks, not interval arithmetic or formal proof.'}
    mp.mp.dps=80
    print('Stage: independent finite products', flush=True)
    products=[]
    for hs,n in [('0.2',1),('0.2',10),('1',3),('0.03',7)]:
        h=mp.mpf(hs)
        finite=(h*n*n+mp.fsum(mp.log(-mp.expm1(-h*j)) for j in range(1,2*n+1))
                -2*mp.fsum(mp.log(-mp.expm1(-h*j)) for j in range(1,n+1)))
        error=exact_log(h,mp.mpf(n))-finite
        assert abs(error)<mp.mpf('1e-65')
        products.append({'h':hs,'n':n,'logarithmic_difference':text(error)})
    report['finite_product_checks']=products
    print('Stage: signed remainders', flush=True)
    signed=[]
    for hs,xs,M in [('0.4','2.5',0),('0.4','2.5',1),('0.1','10',3),('0.001','10',4),('1','3',6)]:
        h=mp.mpf(hs);x=mp.mpf(xs)
        actual=(-1)**(M+1)*(exact_log(h,x)-truncation(h,x,M)-modular(h))
        approx,tail,T,*_=positive_remainder(h,x,M)
        assert 0<actual<T
        assert approx-mp.mpf('1e-65')<actual<approx+tail+mp.mpf('1e-65')
        signed.append({'h':hs,'x':xs,'M':M,'signed_remainder':text(actual),
                       'first_omitted':text(T),'ratio':text(actual/T),
                       'double_sum_error_bound':text(tail)})
    report['signed_remainders']=signed
    print('Stage: optimal truncation', flush=True)
    optimal=[]
    for ts in ['1','6']:
      for hs in ['0.5','0.25','0.125']:
        h=mp.mpf(hs);tau=mp.mpf(ts);x=tau/h;M=int(mp.nint(mp.pi*x))
        R,err,T,*_=positive_remainder(h,x,M)
        a=2*mp.pi*x;d=2*M-a;c=d*d/2-d/2-mp.mpf(5)/12
        leading=mp.exp(-a)/(mp.pi*mp.sqrt(x)); ratio=R/leading
        optimal.append({'h':hs,'tau':ts,'M':M,'R_over_leading':text(ratio),
                        'R_over_next_term':text(R/T),'refined_prediction':text(1+c/a),
                        'relative_double_sum_tail':text(err/R)})
    report['optimal_truncation']=optimal
    print('Stage: inverse cancellation', flush=True)
    profiles=[]
    # Verify a nonlinear inverse equation with a Newton-corrected root.
    for hs in ['0.5','0.25','0.125']:
      mp.mp.dps={'0.5':100,'0.25':140,'0.125':190}[hs]
      h=mp.mpf(hs);r=mp.exp(-4*mp.pi**2/h)
      for ss in (['-1','0','1'] if hs=='0.25' else ['0']):
        s=mp.mpf(ss)
        x=mp.findroot(lambda z:2*mp.pi*z-4*mp.pi**2/h+mp.log(z)/2+mp.log(mp.pi)-s,2*mp.pi/h)
        M=2*int(mp.nint(mp.pi*x/2));target=exact_log(h,x)
        val,slope=truncation(h,x,M,with_slope=True)
        delta=(target-val)/slope; z=x+delta
        # The residual is quadratic in the displacement, unlike a mere coefficient check.
        residual=truncation(h,z,M)-target
        scaled=phase_slope(h*x)*delta/r
        assert abs(residual/r)<mp.mpf('1e-25')
        a=2*mp.pi*x;d=2*M-a;c=d*d/2-d/2-mp.mpf(5)/12
        profiles.append({'h':hs,'s':ss,'x':text(x),'M_even':M,
                         'scaled_inverse_displacement':text(scaled),
                         'leading_profile':text(1-mp.exp(-s)),
                         'refined_zero_window_prediction':text(-c/a) if ss=='0' else None,
                         'nonlinear_residual_over_modular_scale':text(residual/r)})
    report['cancellation_window']=profiles
    mp.mp.dps=75
    print('Stage: multinomial', flush=True)
    multis=[]
    for blocks in [(1,2,3),(1,1,2),(2,2,3)]:
        h=mp.mpf('.2');x=mp.mpf(10);a=min(blocks);rmin=blocks.count(a)
        M=int(mp.nint(mp.pi*a*x));R,err,T,*_=positive_remainder(h,x,M,blocks)
        lead=rmin*mp.exp(-2*mp.pi*a*x)/(2*mp.pi*mp.sqrt(a*x))
        multis.append({'blocks':blocks,'h':'.2','x':'10','M':M,
                       'R_over_shortest_block_prediction':text(R/lead),'relative_tail':text(err/R)})
    report['multinomial']=multis
    # Exact rational coefficients at t=1/2.
    print('Stage: rational Pade', flush=True)
    from sympy.functions.combinatorial.numbers import stirling
    mom=[]
    for j in range(11):
        w=sum(sp.factorial(k)*stirling(2*j+1,k+1,kind=2)*(2-sp.Rational(1,3)**(k+1)) for k in range(2*j+1))
        mom.append(abs(sp.bernoulli(2*j+2))/sp.factorial(2*j+2)*w)
    assert mom[0]==sp.Rational(5,36) and mom[1]==sp.Rational(19,1215)
    coeff=[(-1)**j*m for j,m in enumerate(mom)]
    bounds=[];lastlo=sp.S.Zero;lasthi=mom[0]
    tau=mp.log(2);h=mp.mpf('.5');x=tau/h
    D=(base(h,x)+modular(h)-exact_log(h,x))/h
    for N in range(1,6):
        lo=pade_value(coeff,N-1,N,sp.Rational(1,4))
        hi=pade_value(coeff,N,N,sp.Rational(1,4))
        assert lo<hi and lo>=lastlo and hi<=lasthi
        assert mp.mpf(str(sp.N(lo,70)))<D<mp.mpf(str(sp.N(hi,70)))
        assert sp.det(sp.Matrix(N,N,lambda i,j:mom[i+j]))>0
        bounds.append({'N':N,'lower_exact':str(lo),'upper_exact':str(hi),
                       'lower_decimal':str(sp.N(lo,22)),'upper_decimal':str(sp.N(hi,22)),
                       'width':str(sp.N(hi-lo,14))})
        lastlo,lasthi=lo,hi
    report['pade']={'moments':[str(m) for m in mom],'D_numeric':text(D), 'bounds':bounds}
    report['assertions']='All assertions passed.'
    out=Path(__file__).with_name('results.json');out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    run()
