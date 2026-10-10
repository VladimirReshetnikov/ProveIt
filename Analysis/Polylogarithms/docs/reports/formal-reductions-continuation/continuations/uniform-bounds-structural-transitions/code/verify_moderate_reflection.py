#!/usr/bin/env python3
"""Numerical and finite-symbolic checks for the moderate-reflection theorems.

Outputs are floating-point diagnostics, never interval proofs.  The late
coefficients are obtained from a formal-series recurrence independent of the
saddle approximation. A separate Cauchy quadrature checks selected coefficients.
Moment remainders use direct x=exp(-y) quadrature and are recomputed at higher
precision. Requires mpmath and sympy. Run from any directory.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import mpmath as mp
import sympy as sp

BASE = Path(__file__).resolve().parent


def constants():
    tau = mp.findroot(lambda u: -u*mp.digamma(1-u)-1, (mp.mpf('.5'), mp.mpf('.51')))
    rho = tau/mp.gamma(1-tau)
    v = 1+tau**2*mp.polygamma(1,1-tau)
    b = -mp.loggamma(1+tau)
    kk = lambda z: mp.loggamma(1-mp.exp(z))
    rr = lambda z: mp.log(-mp.loggamma(1+mp.exp(z)))
    r1,r2 = [mp.diff(rr,mp.log(tau),j) for j in (1,2)]
    k3 = mp.diff(kk,mp.log(tau),3)
    delta = r1*r1/(2*v)
    aa = -(r1+r2/2)/v+k3*r1/(2*v*v)
    bb = r2*r1*r1/(2*v*v)-k3*r1**3/(6*v**3)
    return dict(tau=tau,rho=rho,Lambda=-mp.log(rho),v=v,b=b,
                C=tau/mp.sqrt(2*mp.pi*v),r1=r1,r2=r2,k3=k3,
                delta=delta,p1_linear=aa,p1_cubic=bb)


class Coefficients:
    def __init__(self, maxk):
        # a(u)/(gamma*u)=1+q1*u+q2*u^2+..., a=-log Gamma(1+u).
        self.zeta = [mp.mpf(0),mp.euler]+[mp.zeta(j) for j in range(2,maxk+2)]
        q = [mp.mpf(1)]+[(-1)**j*self.zeta[j+1]/((j+1)*mp.euler)
                          for j in range(1,maxk+1)]
        self.loga = [mp.mpf(0)]
        for n in range(1,maxk+1):
            self.loga.append(q[n]-mp.fsum(j*self.loga[j]*q[n-j]
                                          for j in range(1,n))/n)

    def A(self,k,m):
        if m >= k:
            return mp.mpf(0)
        deg = k-1-m
        logcoef = [mp.mpf(0)]+[k*self.zeta[j]/j+m*self.loga[j]
                               for j in range(1,deg+1)]
        ex = [mp.mpf(1)]
        for n in range(1,deg+1):
            ex.append(mp.fsum(j*logcoef[j]*ex[n-j] for j in range(1,n+1))/n)
        return (-1)**(k+m-1)*mp.euler**m*ex[deg]/k


def symbolic_checks():
    xi,r1,r2,k3,v,m,beta0 = sp.symbols('xi r1 r2 k3 v m beta0', real=True)
    I = sp.I
    moments = [sp.Integer(1),I*r1*xi/v]
    for j in range(2,4):
        moments.append(sp.expand(I*r1*xi/v*moments[-1]+(j-1)/v*moments[-2]))
    expected = (-(r1+r2/2)/v+k3*r1/(2*v**2))*xi+(r2*r1**2/(2*v**2)-k3*r1**3/(6*v**3))*xi**3
    actual = I*moments[1]-I*k3*moments[3]/6-xi*r2*moments[2]/2
    assert sp.expand(actual-expected)==0
    fixed = beta0-(2*m*r1+m*r2+m*m*r1*r1)/(2*v)+k3*m*r1/(2*v*v)
    extracted = beta0+m*(-(r1+r2/2)/v+k3*r1/(2*v*v))-m*m*r1*r1/(2*v)
    assert sp.expand(fixed-extracted)==0
    return {'assertions':2,'status':'exact symbolic identities passed',
            'P1':str(sp.expand(expected))}


def cauchy_scaled(k,m,c):
    # Result is A / [(-1)^(k+m-1) C b^m rho^-k k^-3/2].
    tau,rho,b,v = (c[s] for s in ('tau','rho','b','v'))
    def integrand(t):
        u = tau*mp.exp(1j*t)
        Q = mp.gamma(1-u)/mp.gamma(1-tau)*mp.exp(-1j*t)
        return mp.re(Q**k*mp.exp(1j*t)*(-mp.loggamma(1+u)/b)**m)
    value = 2*mp.quad(integrand,[0,1/mp.sqrt(k),3/mp.sqrt(k),mp.mpf('.5'),1,mp.pi])
    return mp.sqrt(k*v/(2*mp.pi))*value


def small_loggamma(x, sign):
    if x == 0:
        return mp.mpf(0)
    if x < mp.mpf('.001'):
        # Number of terms chosen by actual precision and x; no fixed 14-term
        # approximation is reused when the precision is raised.
        terms = max(4,int((mp.mp.dps+20)/(-mp.log10(x)))+2)
        return sign*mp.euler*x+mp.fsum(mp.zeta(j)*(sign*x)**j/j for j in range(2,terms))
    return mp.loggamma(1-sign*x)


def normalized_moment(n,m):
    lf = mp.loggamma(n+1)
    def log_integrand(y):
        if not y:
            return mp.ninf
        x = mp.exp(-y)
        if y < mp.mpf('.125'):
            d = -mp.expm1(-y)
            f = small_loggamma(d,1)
            B = -mp.log(d)+small_loggamma(d,-1)
        else:
            f = y+small_loggamma(x,-1)
            B = small_loggamma(x,1)
        if not f or (m and not B):
            return mp.ninf
        return -y+n*mp.log(f)+(m*mp.log(B) if m else 0)-lf
    mode = mp.mpf(n)/(m+1)
    points = sorted(set([mp.mpf(0),mp.mpf('.125'),mp.mpf('.5'),mp.mpf(1),
                         mode/2,mode,2*mode,4*mode,8*mode]))
    logscale = log_integrand(mode)
    return mp.exp(logscale)*mp.quad(lambda y:mp.exp(log_integrand(y)-logscale),
                                      points+[mp.inf])


def half_row(N,m,dps):
    with mp.workdps(dps):
        c = constants()
        n = int(mp.nint(N*c['Lambda']))
        eta = N*c['Lambda']-n
        coeff = Coefficients(N)
        partial = mp.fsum(coeff.A(k,m)/mp.mpf(k)**n for k in range(1,N))
        omitted = coeff.A(N,m)/mp.mpf(N)**n
        val = normalized_moment(n,m)
        ratio = (val-partial)/omitted
        approx = mp.mpf('.5')+(mp.mpf('1.5')-c['delta']*m*m/N-eta)/(4*N)
        return dict(N=N,n=n,m=m,eta=eta,ratio=ratio,approximation=approx,
                    N32_error=N**mp.mpf('1.5')*(ratio-approx),dps=dps)


def fmt(row):
    return {k:(mp.nstr(v,55) if isinstance(v,(mp.mpf,mp.mpc)) else v) for k,v in row.items()}


def run(args):
    started=time.monotonic()
    mp.mp.dps=args.dps
    out={'status':'analytic proofs are in moderate_reflection.tex; numerics are diagnostics',
         'symbolic':symbolic_checks(),'working_digits':args.dps}
    c=constants()
    out['constants']=fmt(c)
    coeff=Coefficients(max(args.late_k))
    late=[]
    for k in args.late_k:
        for target in (0,1,3,6):
            m=int(mp.nint(target*mp.sqrt(k)))
            if m>=k:
                continue
            xi=mp.mpf(m)/mp.sqrt(k)
            av=coeff.A(k,m)
            lead=(-1)**(k+m-1)*c['C']*c['b']**m*c['rho']**(-k)*mp.mpf(k)**mp.mpf('-1.5')
            rat=av/lead
            damp=mp.exp(-c['delta']*xi*xi)
            p1=c['p1_linear']*xi+c['p1_cubic']*xi**3
            row=dict(k=k,m=m,xi=xi,ratio_to_fixed_leading=rat,gaussian_limit=damp,
                     corrected_ratio=rat/damp,first_correction=1+p1/mp.sqrt(k),
                     k_scaled_corrected_error=k*(rat/damp-1-p1/mp.sqrt(k)))
            if (k,target) in [(args.late_k[0],1),(args.late_k[-1],3)]:
                cq=cauchy_scaled(k,m,c)
                diff=abs(cq-rat)
                assert diff<mp.mpf('1e-40'),(k,m,diff)
                row['independent_cauchy_difference']=diff
            late.append(fmt(row))
            print(json.dumps({'k':k,'m':m,'ratio':mp.nstr(rat,16),'pred':mp.nstr(damp,16),
                              'scaled':mp.nstr(row['k_scaled_corrected_error'],12)}),flush=True)
    out['late_coefficients']=late
    out['status']='in progress: late coefficients complete, moment checks pending'
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    halves=[]
    for N in args.half_N:
        for factor in (1,3):
            m=int(mp.nint(factor*mp.sqrt(N)))
            row=half_row(N,m,args.dps)
            higher=half_row(N,m,args.dps+35)
            difference=abs(row['ratio']-higher['ratio'])
            assert difference<mp.mpf('1e-30'),(N,m,difference)
            row['precision_repeat_difference']=difference
            row['repeat_digits']=args.dps+35
            halves.append(fmt(row))
            print(json.dumps({'N':N,'m':m,'half_ratio':mp.nstr(row['ratio'],18),
                              'prediction':mp.nstr(row['approximation'],18),
                              'scaled':mp.nstr(row['N32_error'],12)}),flush=True)
    out['half_term_diagnostics']=halves
    out['status']='passed: analytic proofs in moderate_reflection.tex; numerics are diagnostics'
    out['runtime_seconds']=round(time.monotonic()-started,3)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'seconds':out['runtime_seconds']}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--dps',type=int,default=180)
    p.add_argument('--late-k',type=int,nargs='+',default=[60,120,240,480])
    p.add_argument('--half-N',type=int,nargs='*',default=[24,48,96])
    p.add_argument('--output',type=Path,default=BASE/'moderate_reflection_checks.json')
    run(p.parse_args())
