#!/usr/bin/env python3
"""Numerical diagnostics, not proof, for the joint log-gamma theorems."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 65
f = mp.loggamma
h = lambda x: -mp.digamma(x) / f(x)
Q = lambda x: h(x)/h(1-x)


def stationary(lam):
    lo, hi = mp.mpf('1e-50'), 1-mp.mpf('1e-50')
    for _ in range(230):
        mid=(lo+hi)/2
        if Q(mid)<lam:
            lo=mid
        else:
            hi=mid
    return (lo+hi)/2


def joint(n,m):
    lam=mp.mpf(m)/n
    x=stationary(lam)
    phase=lambda y:mp.log(f(y))+lam*mp.log(f(1-y))
    top=phase(x)
    kappa=-mp.diff(phase,x,2)
    c1=mp.diff(phase,x,4)/(8*kappa**2)+5*mp.diff(phase,x,3)**2/(24*kappa**3)
    scale=mp.sqrt(n*kappa)
    # Direct normalized integral split at its rigorous unique saddle.
    integrand=lambda y: mp.exp(n*(phase(y)-top))
    val=mp.quad(integrand,[0,x,1])
    lead=mp.sqrt(2*mp.pi/(n*kappa))
    return {'n':n,'m':m,'saddle':str(x),'kappa':str(kappa),
            'leading_relative_error':str(lead/val-1),
            'first_corrected_relative_error':str(lead*(1+c1/n)/val-1),
            'c1':str(c1)}


def critical(m,s):
    n=int(mp.nint((m+1)*(mp.log(m)+s)))
    r=mp.mpf(m+1)
    t=mp.mpf(n)/r
    tau=m*mp.exp(-t)
    shape=n+1
    sd=mp.sqrt(shape)/r
    # Standardized gamma coordinate. Ordinary quadrature below is truncated
    # at T=high+50; it is a diagnostic, not a rigorous integral enclosure.
    lognorm=mp.loggamma(n+1)-(n+1)*mp.log(r)+m*mp.log(mp.euler)
    def log_ratio_integrand(T):
        x=mp.exp(-T)
        return n*mp.log(f(x))+m*mp.log(f(1-x))-T-lognorm
    def integrand(z):
        T=t+sd*z
        if T<=0:
            return mp.mpf(0)
        return sd*mp.exp(log_ratio_integrand(T))
    # The outer numerical subintervals use T coordinates.
    low=max(mp.mpf(0),t-12*sd)
    high=t+12*sd
    central=mp.quad(integrand,[-min(12,t/sd),-6,0,6,12])
    lower=mp.quad(lambda T:mp.exp(log_ratio_integrand(T)),[0,low]) if low else 0
    upper=mp.quad(lambda T:mp.exp(log_ratio_integrand(T)),[high,high+10,high+50])
    exact=central+lower+upper
    c=mp.zeta(2)/(2*mp.euler)
    d=c-mp.euler
    e=mp.euler**2+mp.zeta(3)/(3*mp.euler)-mp.zeta(2)**2/(8*mp.euler**2)
    leading=mp.exp(d*tau)
    correction=(t*(d*tau+d*d*tau*tau)/2-(c+mp.euler)*tau+e*tau*tau)/m
    return {'n':n,'m':m,'s_requested':str(s),'t':str(t),'tau':str(tau),
            'ratio':str(exact),'leading':str(leading),
            'leading_relative_error':str(leading/exact-1),
            'first_corrected_relative_error':str(leading*(1+correction)/exact-1),
            'scaled_second_error':str((leading*(1+correction)/exact-1)*m*m/(t*t))}


if __name__=='__main__':
    result={'arithmetic':'mpmath 65 digits; diagnostics only',
            'joint':[joint(n,m) for n,m in [(20,10),(40,20),(80,40),(20,20),(40,40),(80,80),(20,40),(40,80)]],
            'critical':[critical(m,s) for s in [mp.mpf(-1),mp.mpf(0),mp.mpf(1)] for m in [25,100,400,1600]]}
    (Path(__file__).resolve().parents[1] / "results" / "gamma_joint_diagnostics.json").write_text(json.dumps(result,indent=2)+'\n')
    for row in result['joint']:
        print('joint',row['n'],row['m'],row['leading_relative_error'][:16],row['first_corrected_relative_error'][:16])
    for row in result['critical']:
        print('critical',row['n'],row['m'],row['s_requested'],row['leading_relative_error'][:16],row['first_corrected_relative_error'][:16],row['scaled_second_error'][:16])
