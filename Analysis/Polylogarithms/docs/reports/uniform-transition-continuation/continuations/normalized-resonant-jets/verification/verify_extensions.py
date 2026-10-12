#!/usr/bin/env python3
"""Checks for the beta kernel, bounded resonance window, and exact order tuning.

The finite algebraic checks are exact; all analytic comparisons are ordinary
80-digit floating-point diagnostics, not interval certificates. No network is
used. The article contains the proofs. Run with --output-dir to preserve data.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import platform
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def hurwitz(s, a):
    if a == mp.mpf('0.5'):
        return mp.expm1(s*mp.log(2))*mp.zeta(s)
    return mp.zeta(s, a)


def D(m, e):
    return mp.fprod(1+e/j for j in range(1,m+1))/mp.gamma(1-e)


def generating_tail(m, a, e, t, terms=40):
    return D(m,e)*mp.fsum((-1)**n*mp.factorial(m)/mp.factorial(m+n)*
                 hurwitz(1+e-n,a)*t**n for n in range(1,terms+1))


def generating_direct(m, a, e, t):
    s=m+1+e
    if a == 1:
        value=mp.polylog(s,mp.exp(-t))
    elif a == mp.mpf('0.5'):
        value=2**s*mp.polylog(s,mp.exp(-t/2))-mp.polylog(s,mp.exp(-t))
    else:
        value=mp.exp(-a*t)*mp.lerchphi(mp.exp(-t),s,a)
    polynomial=mp.fsum(hurwitz(s-k,a)*(-t)**k/mp.factorial(k) for k in range(m))
    counter=(mp.harmonic(m)-mp.euler-mp.digamma(a) if e == 0
             else D(m,e)*hurwitz(1+e,a)-1/e)
    return (-1)**m*mp.factorial(m)*D(m,e)*(value-polynomial)-t**m*counter


def R(z):
    return mp.mpf(1) if not z else -mp.expm1(-z)/z


def E(z):
    return mp.mpf(1) if not z else mp.expm1(z)/z


def tuned_order(m, v, terms=40):
    # D is a nonzero factor; omitting it avoids artificial root conditioning.
    def divided_tail(e):
        return mp.fsum((-1)**n*mp.factorial(m)/mp.factorial(m+n)*
                  hurwitz(1+e-n,mp.mpf('0.5'))*v**(n-1)
                  for n in range(1,terms+1))
    seed=-v/(12*(m+2)*mp.log(2))
    return mp.findroot(divided_tail,(seed,seed*(1+mp.mpf('0.001'))),tol=mp.mpf('1e-73'))


def run(outdir):
    start=time.monotonic();mp.mp.dps=80
    exact=0;rows=[];tuning=[]
    # Symbolic computation from an independent implicit-series substitution.
    h,l2,l2pi,zp,k1,k2,v=sp.symbols('h l2 l2pi zp k1 k2 v')
    for m in range(1,9):
        b11=l2/(2*(m+1))
        b12=l2/(m+1)*(h+l2pi+l2/2)
        b20=sp.Rational(1,24*(m+1)*(m+2))
        b21=((h-l2)/24-zp/2)/((m+1)*(m+2))
        want1=-1/(12*(m+2)*l2)
        want2=-(l2pi+sp.Rational(3,2)*l2+12*zp)/(144*(m+2)**2*l2**2)
        expression=b11*(want1*v+want2*v**2)+b12*(want1*v)**2/2+b20*v+b21*want1*v**2
        if sp.expand(expression).coeff(v,1)!=0 or sp.simplify(sp.expand(expression).coeff(v,2))!=0:
            raise AssertionError('Cancellation-curve coefficient identity failed')
        exact+=1
    def compare(kind,params,left,right,tol='1e-55'):
        error=abs(left-right)/max(mp.mpf(1),abs(left),abs(right))
        if error>=mp.mpf(tol):
            raise AssertionError((kind,params,mp.nstr(error,20)))
        rows.append({'kind':kind,**params,'scaled_absolute_error':mp.nstr(error,20)})
    print('Exact coefficient identities passed',flush=True)
    # Independent real beta integral versus the convergent Hurwitz tail.
    for m in (1,2,4):
        for a in (mp.mpf(1),mp.mpf('0.5'),mp.mpf(1)/3):
            t=mp.mpf('0.7')
            def integrand(u):
                if u == 0:
                    return (a-mp.mpf('0.5'))*t
                x=u*t
                kernel=x*mp.exp((1-a)*x)/mp.expm1(x)
                return (1-u)**m*(1-kernel)/u
            integral=mp.quad(integrand,[0,mp.mpf('.5'),1])
            compare('beta_kernel',{'m':m,'a':mp.nstr(a,20)},integral,
                    generating_tail(m,a,mp.mpf(0),t,terms=68))
    print('Beta-kernel diagnostics passed',flush=True)
    # The full normalized implicit equation, independently evaluated from Li.
    for m in (1,3):
        for a in (mp.mpf(1),mp.mpf('0.5')):
            for z in (mp.mpf(-1),mp.mpf(0),mp.mpf(1)):
                L=mp.mpf(10);w=1/L;v0=mp.exp(-L);e=z*w
                u=mp.mpf('0.0003');t=v0*(1+u)
                y=v0**m*L*R(z)
                logu=mp.log1p(u); hz=mp.exp(-z)/R(z)
                chart=(1+u)**m*(1-w*hz*logu*E(z*w*logu)+
                        w*generating_tail(m,a,e,t)/R(z))
                actual=generating_direct(m,a,e,t)/y
                compare('bounded_resonance_chart',{'m':m,'a':str(a),'z':str(z)},actual,chart,'1e-52')
    print('Resonance-chart diagnostics passed',flush=True)
    # Exact tuning is solved using the series and checked with direct polylogs.
    zp1=mp.diff(mp.zeta,-1)
    for m in (1,2,5):
        for vv in ('0.04','0.02','0.01'):
            v0=mp.mpf(vv); e=tuned_order(m,v0)
            c1=-1/(12*(m+2)*mp.log(2))
            c2=-(mp.log(2*mp.pi)+mp.mpf('1.5')*mp.log(2)+12*zp1)/(144*(m+2)**2*mp.log(2)**2)
            predicted=c1*v0+c2*v0*v0
            core=v0**m*(-mp.expm1(e*mp.log(v0)))/e
            direct=generating_direct(m,mp.mpf('0.5'),e,v0)
            compare('exact_order_tuning',{'m':m,'v':vv},direct,core,'1e-56')
            print(f'Tuning checked: m={m}, v={vv}',flush=True)
            tuning.append({'m':m,'v':vv,'epsilon_star':mp.nstr(e,45),
                           'two_term_approximation':mp.nstr(predicted,45),
                           'two_term_error_div_v_cubed':mp.nstr((e-predicted)/v0**3,20),
                           'direct_core_scaled_error':mp.nstr(abs(direct-core)/max(1,abs(core)),20)})
    result={'exact_assertions_passed':exact,'numerical_comparisons_passed':len(rows),
            'precision_digits':80,'numerical_status':'Floating-point diagnostics, not interval certificates',
            'seconds':round(time.monotonic()-start,3),'python':platform.python_version(),
            'mpmath':mp.__version__,'sympy':sp.__version__,'comparisons':rows,'tuning_rows':tuning}
    outdir.mkdir(parents=True,exist_ok=True)
    (outdir/'extension_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    return {k:val for k,val in result.items() if k not in ('comparisons','tuning_rows')}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=Path,default=ROOT/'data')
    args=p.parse_args()
    print(json.dumps(run(args.output_dir),indent=2))
