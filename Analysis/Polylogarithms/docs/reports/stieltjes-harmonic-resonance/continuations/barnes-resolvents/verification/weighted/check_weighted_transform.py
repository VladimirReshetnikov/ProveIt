#!/usr/bin/env python3
"""Independent numerical diagnostics for the polynomial Hurwitz resolvent.

The lattice side sums the subtracted U_j,V_j Dirichlet series, with an
explicit binomial expansion of their inner tails into Hurwitz zeta and its
first order derivative, evaluated by scaled Euler--Maclaurin summation.
The other side uses direct x-quadrature of the
Hurwitz function or digamma. No original author's evaluator is imported.

Dependencies: mpmath. Run from any directory:
    python /path/to/check_weighted_transform.py
Results are written next to this file. These are non-interval diagnostics.
"""
from __future__ import annotations

import json
import platform
from pathlib import Path
import time
import mpmath as mp

mp.mp.dps = 65
N_OUTER = 105
M_TAIL = 256
K_TAIL = 48
K_EM = 40
OUT = Path(__file__).with_name('weighted_transform_results.json')


def repr_complex(v, digits=57):
    return {'real': mp.nstr(mp.re(v), digits), 'imag': mp.nstr(mp.im(v), digits)}


def coords(eps, q):
    omega = eps*2j*mp.pi
    sigma = -omega
    z = eps*1j*mp.pi*(1+q)/(1-q)
    a = z+eps*1j*mp.pi
    c = omega/(a*a)
    return z, a, c, omega, sigma


def polylog_value_and_order_derivative(s, q):
    terms = [q**n/mp.power(n,s) for n in range(1,N_OUTER+1)]
    return mp.fsum(terms), -mp.fsum(mp.log(n)*terms[n-1] for n in range(1,N_OUTER+1))


def hurwitz_tail_and_derivative(p, M):
    """Euler--Maclaurin evaluation of zeta(p,M) and its order derivative.

    Factoring M**(1-p) preserves relative precision even when the tail is
    extremely small. Direct mp.zeta(p,M) can lose relative precision in
    that regime, which is then amplified by the binomial coefficients.
    The derivative is taken analytically in this finite expansion.
    This asymptotic tail computation is a diagnostic, not an interval bound.
    """
    M = mp.mpf(M)
    h = 1/(p-1)+1/(2*M)
    hp = -1/(p-1)**2
    rf = mp.mpc(1)
    rfp = mp.mpc(0)
    for ell in range(1, 2*K_EM):
        rf, rfp = rf*(p+ell-1), rfp*(p+ell-1)+rf
        if ell % 2:
            k = (ell+1)//2
            coeff = mp.bernoulli(2*k)/mp.factorial(2*k)/M**(2*k)
            h += coeff*rf
            hp += coeff*rfp
    scale = M**(1-p)
    return scale*h, scale*(hp-mp.log(M)*h)


def subtracted_lattice(s, q, degree):
    """U_j,V_j and their s derivatives, j=1,...,degree.

    For m >= M_TAIL > N_OUTER, expand (m+n)^(-alpha) in n/m.
    k=0 cancels the defining subtraction identically. The remaining
    infinite m sums are zeta(s+j+k,M_TAIL), with their derivatives.
    Differentiate the rising-factorial coefficient as well for V_j.
    """
    logs = [mp.mpf(0)]+[mp.log(n) for n in range(1,M_TAIL+N_OUTER+1)]
    powers = [mp.mpf(0)]+[mp.exp(-s*logs[n]) for n in range(1,M_TAIL+N_OUTER+1)]
    ans = {}
    for j in range(1,degree+1):
        tails = [hurwitz_tail_and_derivative(s+j+k, M_TAIL)
                 for k in range(1, K_TAIL+1)]
        hz = [mp.mpc(0)]+[v for v, dv in tails]
        hzp = [mp.mpc(0)]+[dv for v, dv in tails]
        inv = [mp.mpf(0)]+[mp.mpf(n)**(-j) for n in range(1,M_TAIL+N_OUTER+1)]
        U=[]; Up=[]; V=[]; Vp=[]
        for n in range(1,N_OUTER+1):
            u=[]; up=[]; v=[]; vp=[]
            for m in range(1,M_TAIL):
                ut = powers[m]*(inv[m+n]-inv[m])
                vt = inv[m]*(powers[m+n]-powers[m])
                u.append(ut)
                up.append(-logs[m]*ut)
                v.append(vt)
                vp.append(inv[m]*(-logs[m+n]*powers[m+n]+logs[m]*powers[m]))
            cu=mp.mpc(1); cv=mp.mpc(1); cvp=mp.mpc(0)
            for k in range(1,K_TAIL+1):
                cu *= -mp.mpf(n)*(j+k-1)/k
                cv,cvp = (-mp.mpf(n)*(s+k-1)*cv/k,
                          -mp.mpf(n)*((s+k-1)*cvp+cv)/k)
                u.append(cu*hz[k])
                up.append(cu*hzp[k])
                v.append(cv*hz[k])
                vp.append(cvp*hz[k]+cv*hzp[k])
            qn=q**n
            U.append(qn*mp.fsum(u)); Up.append(qn*mp.fsum(up))
            V.append(qn*mp.fsum(v)); Vp.append(qn*mp.fsum(vp))
        ans[j] = tuple(mp.fsum(x) for x in (U,Up,V,Vp))
    return ans


def bracket(s, eps, q, degree):
    z,a,c,omega,sigma=coords(eps,q)
    mu=mp.mpf(1)/(degree+1)
    bs={j:(-1)**(j-1)*mp.factorial(degree)/mp.factorial(degree-j+1)/omega**j
        for j in range(1,degree+1)}
    Li,Lip=polylog_value_and_order_derivative(s,q)
    Lij={j:polylog_value_and_order_derivative(j,q)[0] for j in bs}
    lattice=subtracted_lattice(s,q,degree)
    lo=mp.log(omega); ls=mp.log(sigma)
    op=mp.exp(-s*lo); sp=mp.exp(-s*ls)
    B=sp*mu*Li
    Bp=sp*mu*(Lip-ls*Li)
    for j,b in bs.items():
        U,Up,V,Vp=lattice[j]
        B+=b*(op*U+sp*(Li*Lij[j]+(-1)**j*V))
        Bp+=b*(op*(Up-lo*U)+sp*((Lip-ls*Li)*Lij[j]+(-1)**j*(Vp-ls*V)))
    Bzero=mu*q/(1-q)-mp.fsum(bs[j]*Lij[j] for j in bs)
    return B,Bp,Bzero,(z,a,c,omega,sigma)


def quadrature(s,z,degree,derivative=False,stieltjes=False):
    def integrand(x):
        if x==0 or x==1:
            return mp.mpc(0)
        R=1/(mp.pi*mp.cot(mp.pi*x)-z)
        if stieltjes:
            f=-mp.digamma(x)
        elif derivative:
            f=-mp.zeta(1-s,x,derivative=1)
        else:
            f=mp.zeta(1-s,x)
        return x**degree*f*R
    return mp.quad(integrand,[0,mp.mpf('.1'),mp.mpf('.35'),mp.mpf('.65'),mp.mpf('.9'),1])


def record(name,series,direct,**extra):
    residual=abs(series-direct)
    return {'name':name,'lattice_value':repr_complex(series),'direct_quadrature':repr_complex(direct),
            'absolute_residual':mp.nstr(residual,12),
            'scaled_residual':mp.nstr(residual/max(1,abs(direct)),12),**extra}


def main():
    start=time.time()
    rows=[]
    cases=[('linear_upper',1,1,mp.mpc('.2','.1'),mp.mpc('1.7','.2')),
           ('quadratic_lower',2,-1,mp.mpc('-.25','.05'),mp.mpc('2.3','-.15'))]
    for name,degree,eps,q,s in cases:
        B,Bp,Bzero,(z,a,c,omega,sigma)=bracket(s,eps,q,degree)
        I=c*mp.gamma(s)*B/q
        Ip=c*mp.gamma(s)*(Bp+mp.digamma(s)*B)/q
        metadata={'polynomial':'x' if degree==1 else 'x^2','epsilon':eps,
                  'q':repr_complex(q),'z':repr_complex(z),'s':repr_complex(s)}
        rows.append(record(name+'_value',I,quadrature(s,z,degree),**metadata))
        rows.append(record(name+'_spectral_derivative',Ip,quadrature(s,z,degree,derivative=True),**metadata))
    # The weighted Stieltjes check exercises the actual subtracted series at s=0.
    degree,eps,q=2,-1,mp.mpc('-.25','.05')
    B,Bp,Bzero,(z,a,c,omega,sigma)=bracket(mp.mpf(0),eps,q,degree)
    moment=c*(Bp-mp.euler*Bzero)/q
    rows.append(record('quadratic_lower_stieltjes_m0',moment,quadrature(None,z,degree,stieltjes=True),
                       polynomial='x^2',epsilon=eps,q=repr_complex(q),z=repr_complex(z),m=0))
    report={'purpose':'Independent polynomial Hurwitz resolvent diagnostics',
            'status':'Non-interval numerical agreement; no residual is a proof or certified bound.',
            'python':platform.python_version(),'mpmath':mp.__version__,'precision_dps':mp.mp.dps,
            'outer_n_max':N_OUTER,'inner_tail_starts_at':M_TAIL,'binomial_tail_terms':K_TAIL,
            'euler_maclaurin_terms':K_EM,
            'series_method':'Direct U_j,V_j differences, then binomial tails and scaled Euler--Maclaurin Hurwitz values and derivatives.',
            'direct_method':'x-quadrature of Hurwitz zeta, its first spectral derivative, or -digamma.',
            'checks':rows,'s0_Bzero_identity_residual':mp.nstr(abs(B-Bzero),12),
            'all_scaled_residuals_below_1e_30':all(mp.mpf(x['scaled_residual'])<mp.mpf('1e-30') for x in rows),
            'elapsed_seconds':round(time.time()-start,3)}
    OUT.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'checks':len(rows),'maximum_absolute_residual':max(rows,key=lambda x:mp.mpf(x['absolute_residual']))['absolute_residual'],
                      'all_scaled_residuals_below_1e_30':report['all_scaled_residuals_below_1e_30'],
                      'elapsed_seconds':report['elapsed_seconds'],'output':str(OUT)},indent=2))
    assert report['all_scaled_residuals_below_1e_30']


if __name__=='__main__':
    main()
