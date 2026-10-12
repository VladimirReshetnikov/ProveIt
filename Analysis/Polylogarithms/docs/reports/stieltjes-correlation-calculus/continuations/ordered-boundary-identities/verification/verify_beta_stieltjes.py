#!/usr/bin/env python3
"""Independent symbolic and numerical checks of beta--Stieltjes jets."""
from functools import lru_cache
from pathlib import Path
from math import comb, factorial
import json
import time

import mpmath as mp
import sympy as sp


def exact_bell_checks():
    v=sp.symbols('v')
    ell=sp.symbols('ell1:5')
    g=sp.symbols('g0:5')
    B=[sp.Integer(1)]
    for n in range(4):
        B.append(sp.expand(sum(comb(n,k)*B[n-k]*ell[k] for k in range(n+1))))
    exponential=sp.exp(sum(ell[k-1]*v**k/sp.factorial(k) for k in range(1,5))).series(v,0,5).removeO()
    germ=sum((-1)**j*g[j]*v**j/sp.factorial(j) for j in range(5))
    for m in range(5):
        derivative=sp.expand(exponential*germ).coeff(v,m)*factorial(m)
        formula=sum(comb(m,j)*(-1)**j*B[m-j]*g[j] for j in range(m+1))
        assert sp.expand(derivative-formula)==0
    return 5


def prepare_stieltjes_differences(R=201):
    zs=[]
    coefficients=[[],[],[]]
    H=mp.mpf(0)
    H2=mp.mpf(0)
    for r in range(1,R+1):
        H+=mp.mpf(1)/r
        H2+=mp.mpf(1)/(r*r)
        if r%2==0:
            continue
        values=[mp.diff(lambda w:mp.zeta(w,2),r+1,m) for m in range(3)]
        z0,z1,z2=values
        zs.append((r,values))
        coefficients[0].append(-2*z0)
        coefficients[1].append(2*(H*z0+z1))
        coefficients[2].append(-2*((H*H-H2)*z0+2*H*z1+z2))
    reverse=[tuple(reversed(c)) for c in coefficients]
    @lru_cache(maxsize=None)
    def delta_gamma(u):
        u2=u*u
        return tuple(u*mp.polyval(c,u2) for c in reverse)
    return zs,delta_gamma


def spot_checks(delta_gamma):
    rows=[]
    for u in map(mp.mpf,['0.1','0.6','0.95']):
        approximations=delta_gamma(u)
        for m in range(3):
            direct=mp.stieltjes(m,2+u)-mp.stieltjes(m,2-u)
            error=abs(direct-approximations[m])
            assert error<mp.mpf('1e-35')
            rows.append(dict(u=str(u),m=m,absolute_error=mp.nstr(error,12)))
    return rows


def hurwitz_value(sigma,m,zs):
    return -2*mp.fsum(mp.rf(sigma,r)/mp.factorial(r)*values[m] for r,values in zs)


def beta_integral(sigma,m,delta_gamma):
    c1=mp.digamma(1)-mp.digamma(1-sigma)
    c2=mp.polygamma(1,1)-mp.polygamma(1,1-sigma)
    def integrand(z):
        if z>=0:
            ez=mp.exp(-z)
            u=1/(1+ez)
            weight=mp.exp(-(1-sigma)*z)/(1+ez)
            log1mu=-z-mp.log1p(ez)
        else:
            ez=mp.exp(z)
            u=ez/(1+ez)
            weight=mp.exp(sigma*z)/(1+ez)
            log1mu=-mp.log1p(ez)
        ell1=log1mu+c1
        g0,g1,g2=delta_gamma(u)
        if m==0:
            value=g0
        elif m==1:
            value=ell1*g0-g1
        else:
            value=(ell1*ell1+c2)*g0-2*ell1*g1+g2
        return weight*value
    # At sigma in {.3,.5,.7}, these finite endpoints leave exponential
    # tails well below 10^(-38), including the quadratic log factor.
    integral=mp.quad(integrand,[-120,-20,0,20,120,360])
    return mp.sin(mp.pi*sigma)/mp.pi*integral


def direct_partial(sigma,m,N=4000):
    return mp.fsum(((k+3)**(-sigma)-(k+1)**(-sigma))
                   *(k+2)**(sigma-1)*(-mp.log(k+2))**m
                   for k in range(N+1))


def independent_shift_checks():
    a,b,sigma=map(mp.mpf,['0.7','1.1','0.4'])
    y=b+1
    dplus=a-b+1
    dminus=a-b-1
    R=351
    coefficients=[[],[],[]]
    series=[mp.mpf(0),mp.mpf(0),mp.mpf(0)]
    H=mp.mpf(0)
    H2=mp.mpf(0)
    for r in range(1,R+1):
        H+=mp.mpf(1)/r
        H2+=mp.mpf(1)/(r*r)
        z=[mp.diff(lambda w:mp.zeta(w,y),r+1,m) for m in range(3)]
        shift=(-1)**r*(dplus**r-dminus**r)
        coefficients[0].append(shift*z[0])
        coefficients[1].append(-shift*(H*z[0]+z[1]))
        coefficients[2].append(shift*((H*H-H2)*z[0]+2*H*z[1]+z[2]))
        order=mp.rf(sigma,r)/mp.factorial(r)
        for m in range(3):
            series[m]+=shift*order*z[m]
    reverse=[tuple(reversed(c)) for c in coefficients]
    @lru_cache(maxsize=None)
    def delta_gamma(u):
        return tuple(u*mp.polyval(c,u) for c in reverse)
    u=mp.mpf('0.6')
    spots=[]
    for m,approx in enumerate(delta_gamma(u)):
        direct=mp.stieltjes(m,y+dplus*u)-mp.stieltjes(m,y+dminus*u)
        error=abs(direct-approx)
        assert error<mp.mpf('1e-35')
        spots.append(mp.nstr(error,12))
    rows=[]
    for m in range(3):
        integral=beta_integral(sigma,m,delta_gamma)
        error=abs(integral-series[m])
        assert error<mp.mpf('1e-32')
        partial=mp.fsum(((k+a+2)**(-sigma)-(k+a)**(-sigma))
                       *(k+y)**(sigma-1)*(-mp.log(k+y))**m
                       for k in range(4001))
        rows.append(dict(a=str(a),b=str(b),sigma=str(sigma),m=m,
                         hurwitz_series=mp.nstr(series[m],38),
                         beta_stieltjes_integral=mp.nstr(integral,38),
                         absolute_error=mp.nstr(error,12),
                         original_partial=mp.nstr(partial,30),
                         original_partial_discrepancy=mp.nstr(partial-series[m],12)))
    # The same elementary integral bounds give coefficient majorant
    # (4r^2+10r+18)*(2/3)^r for these particular shifts.
    rho=mp.mpf(2)/3
    r=R+1
    sum0=rho**r/(1-rho)
    sum1=rho**r*(r/(1-rho)+rho/(1-rho)**2)
    sum2=rho**r*(r*r/(1-rho)+2*r*rho/(1-rho)**2
                +rho*(1+rho)/(1-rho)**3)
    tail=4*sum2+10*sum1+18*sum0
    assert tail<mp.mpf('1e-54')
    return dict(Taylor_last_degree=R,uniform_omitted_tail_bound=mp.nstr(tail,12),
                direct_stieltjes_spot_errors=spots,jet_checks=rows)


def main():
    start=time.time()
    mp.mp.dps=42
    exact=exact_bell_checks()
    zs,delta_gamma=prepare_stieltjes_differences()
    spots=spot_checks(delta_gamma)
    rows=[]
    for sigma in map(mp.mpf,['0.3','0.5','0.7']):
        for m in range(3):
            lhs=hurwitz_value(sigma,m,zs)
            rhs=beta_integral(sigma,m,delta_gamma)
            error=abs(lhs-rhs)
            assert error<mp.mpf('1e-32'),(sigma,m,lhs,rhs,error)
            partial=direct_partial(sigma,m)
            rows.append(dict(sigma=str(sigma),m=m,hurwitz_series=mp.nstr(lhs,38),
                             beta_stieltjes_integral=mp.nstr(rhs,38),
                             absolute_error=mp.nstr(error,12),N=4000,
                             original_partial=mp.nstr(partial,30),
                             original_partial_discrepancy=mp.nstr(partial-lhs,12)))
    half=hurwitz_value(mp.mpf('0.5'),0,zs)
    half_error=abs(half+1/mp.sqrt(2))
    assert half_error<mp.mpf('1e-35')
    shifted=independent_shift_checks()
    # Uniform bound stated in the audit note, with R=202.
    R=202
    omitted_bound=(3*(R*R+2*R+3)+10*(R+1)+15)*mp.power(2,1-R)
    assert omitted_bound<mp.mpf('1e-54')
    report=dict(working_decimal_precision=42,
                exact_Bell_Leibniz_coefficients=exact,
                stieltjes_Taylor_last_odd_degree=201,
                uniform_omitted_Stieltjes_tail_bound=mp.nstr(omitted_bound,12),
                direct_stieltjes_spot_checks=spots,
                beta_Stieltjes_jet_checks=rows,
                independent_shift_checks=shifted,
                half_order_telescoping_error=mp.nstr(half_error,12),
                elapsed_seconds=round(time.time()-start,3),
                interpretation=('Symbolic coefficient checks are exact. '
                                'Integrals and sums are numerical diagnostics. '
                                'The beta integrand uses uniformly convergent '
                                'Stieltjes Taylor polynomials spot-checked against '
                                'direct mpmath.stieltjes evaluations; it is '
                                'integrated numerically, not by beta moments.'))
    out=Path(__file__).with_name('beta_stieltjes_checks.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
