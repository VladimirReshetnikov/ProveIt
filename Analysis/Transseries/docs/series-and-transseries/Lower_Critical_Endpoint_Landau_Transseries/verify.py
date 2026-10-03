#!/usr/bin/env python3
"""Reproducible finite audits for the lower-endpoint research article.

Exact checks use Fraction/SymPy. Other checks are floating-point diagnostics,
not interval certificates. No network requests are performed. Outputs go to
--output (default: build/verification), leaving the recorded data/ untouched.
"""
from __future__ import annotations
import argparse, cmath, csv, json, math, platform
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import exp1
import sympy as sp
import mpmath as mp


def mul(a, b, n):
    out = [F(0)] * (n+1)
    for i, x in enumerate(a[:n+1]):
        for j, y in enumerate(b[:n+1-i]): out[i+j] += x*y
    return out


def exp_series(a, n):
    assert a[0] == 0
    b = [F(1)] + [F(0)]*n
    for k in range(1, n+1):
        b[k] = sum((j*a[j]*b[k-j] for j in range(1,k+1)), F(0))/k
    return b


def exact_audit():
    n = 12
    checks, coeffs = [], {}
    for c in [F(1,3), F(1,2), F(2)]:
        # Direct iteration of U = c sum q^j exp(j U)/j^2.
        u = [F(0)]*(n+1)
        for _ in range(n):
            v = [F(0)]*(n+1)
            for j in range(1,n+1):
                e = exp_series([j*x for x in u], n-j)
                for k in range(n-j+1): v[k+j] += c*e[k]/(j*j)
            u = v
        for k in range(1,n+1):
            a = [F(0)]+[k*c/F(j*j) for j in range(1,k+1)]
            lag = exp_series(a,k)[k]/k
            assert lag == u[k]
            checks.append(f"fixed_point_vs_Lagrange:c={c},n={k}")
        coeffs[str(c)] = [str(x) for x in u]
    s,d,lam=sp.symbols('s d lam')
    r1 = -s/2+s**2/4
    r2 = (3*s-s**3)/72
    P = sp.series(sp.exp(-lam*(d*r1+d**2*r2)),d,0,3).removeO().expand()
    assert sp.simplify(P.coeff(d,1)-lam*(s-s*s/2)/2)==0
    assert sp.simplify(P.coeff(d,2)+lam*(3*s-s**3)/72-lam**2*(s-s*s/2)**2/8)==0
    checks += ['first_coefficient_polynomial','second_coefficient_polynomial']
    s1 = r1/sp.log(s)
    assert sp.simplify(-sp.log(s)*s1+r1)==0
    checks.append('Lambert_chart_first_correction')
    # Exact derivative of the normal form, through d^7, including fold curvature.
    R = sum((-1)**k*sp.zeta(2-k)*d**(k-1)*(k*s-s**k)/sp.factorial(k) for k in range(2,9))
    assert sp.diff(R,s).subs(s,1)==0
    assert sp.series(-1+sp.diff(R,s,2).subs(s,1)+d/(sp.exp(d)-1),d,0,8).removeO()==0
    checks += ['exact_fold_stationarity_through_order_7','fold_curvature_through_order_7']
    assert sp.expand(R.subs(s,1)).coeff(d,1)==-sp.Rational(1,4)
    assert sp.expand(R.subs(s,1)).coeff(d,2)==sp.Rational(1,36)
    checks += ['fold_value_delta_coefficient','fold_value_delta_squared_coefficient']
    return {'passed':len(checks),'checks':checks,'coefficients':coeffs}


def profile_moment(lam: float, degree: int=0):
    def fun(u):
        s=1+1j*u
        return (s**degree*cmath.exp(lam*(s*cmath.log(s)-s))).real/math.pi
    value,err=quad(fun,0,np.inf,epsabs=2e-13,epsrel=2e-12,limit=1000)
    return value,err


def scaled_H(lam: float):
    # e^lambda sqrt(2*pi*lambda) H(lambda), avoids underflow for large lambda.
    def fun(v):
        s=1+1j*v/math.sqrt(lam)
        exponent=lam*(s*cmath.log(s)-s+1)
        return math.sqrt(2/math.pi)*cmath.exp(exponent).real
    return quad(fun,0,np.inf,epsabs=2e-12,epsrel=2e-12,limit=500)[0]


def profile_ratio(lam: float, m: float):
    # Killed characteristic function: keeping the full centering is essential.
    def fun(u):
        s=1-1j*u
        tail=cmath.exp(-s*m)/m-s*exp1(s*m)
        return cmath.exp(lam*(s*cmath.log(s)+1j*u-tail)).real/math.pi
    numerator,error=quad(fun,0,np.inf,epsabs=2e-12,epsrel=2e-11,limit=1000)
    h,_=profile_moment(lam)
    return numerator/(math.exp(lam)*h),error


def saddle_parameters(n: int, lam: float):
    def coupling(d):return -1/math.log(-math.expm1(-d))
    d=brentq(lambda x:n*coupling(x)*x-lam,1e-12,0.9,xtol=2e-15)
    return d,coupling(d)


def probabilities(n: int,c:float,d:float,max_action:int|None=None):
    # Normalized compound-Poisson recurrence, with the full zero-event factor.
    LD=np.longdouble
    j=np.arange(1,n+1,dtype=LD)
    a=LD(n)*LD(c)*np.exp(-LD(d)*j)/j
    if max_action is not None and max_action<n:a[max_action:]=0
    mp.mp.dps=40
    intensity=mp.mpf(n)*mp.mpf(c)*mp.polylog(2,mp.exp(-mp.mpf(d)))
    p=np.zeros(n+1,dtype=LD)
    p[0]=np.exp(-LD(str(intensity)))
    if p[0]==0:
        raise ArithmeticError('longdouble exponent range insufficient; use a wider precision platform')
    for k in range(1,n+1):p[k]=np.dot(a[:k],p[k-1::-1])/k
    return p[n]


def normal_form_checks():
    mp.mp.dps=90
    rows=[]
    for eps in [mp.mpf('0'),mp.mpf('.001'),mp.mpf('.03'),mp.mpf('.2')]:
        for d in [mp.mpf('.005'),mp.mpf('1e-8')]:
            c=1/mp.polylog(1+eps,mp.exp(-d)); A=c*mp.gamma(1-eps)*d**eps
            for s in [mp.mpf('.7'),mp.mpf('2.1'),1+2j]:
                exact=(-d*s-c*(mp.polylog(2+eps,mp.exp(-d*s))-mp.zeta(2+eps)))/(A*d)
                base=s*(1-mp.log(s)) if eps==0 else (s-s**(1+eps)/(1+eps))/eps
                tail=sum((-1)**k*mp.zeta(2+eps-k)*d**(k-1-eps)*(k*s-s**k)/mp.factorial(k) for k in range(2,19))/mp.gamma(1-eps)
                error=abs(exact-base-tail)
                assert error < mp.mpf('1e-39')
                rows.append({'epsilon':str(eps),'delta':str(d),'s':str(s),'error':mp.nstr(error,8)})
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('build/verification'))
    parser.add_argument('--max-n',type=int,default=2048)
    args=parser.parse_args()
    if args.max_n<128:parser.error('--max-n must be at least 128')
    out=args.output;out.mkdir(parents=True,exist_ok=True)
    exact=exact_audit();normal=normal_form_checks()
    table=[];cuts=[];profiles=[]
    ns=sorted(set([128,512,args.max_n]))
    for lam in [.25,1.,4.]:
        moments=[profile_moment(lam,k)[0] for k in range(5)]
        h=moments[0]
        C1=lam/2*(moments[1]-moments[2]/2)
        C2=-lam*(3*moments[1]-moments[3])/72+lam**2/8*(moments[2]-moments[3]+moments[4]/4)
        profiles.append({'lambda':lam,'H':h,'C1':C1,'C2':C2})
        for n in ns:
            d,c=saddle_parameters(n,lam)
            p=probabilities(n,c,d)
            mp.mp.dps=50
            dd,cc=mp.mpf(d),mp.mpf(c)
            dq=-dd-cc*(mp.polylog(2,mp.exp(-dd))-mp.zeta(2))
            value=float(np.exp(-np.longdouble(str(n*dq)))*p/np.longdouble(d))
            err0=value/h-1;err1=(value-h-d*C1)/h;err2=(value-h-d*C1-d*d*C2)/h
            table.append({'lambda':lam,'n':n,'delta':d,'c':c,'normalized_coefficient':value,'relative_error_0':err0,'relative_error_1':err1,'relative_error_2':err2})
            assert abs(err0)<.2
            if n==args.max_n:
                for m in [.5,1.,2.]:
                    M=max(1,round(m/d));meff=M*d
                    ratio=float(probabilities(n,c,d,M)/p)
                    limit,error=profile_ratio(lam,meff)
                    cuts.append({'lambda':lam,'n':n,'M':M,'M_delta':meff,'ratio':ratio,'limiting_ratio':limit,'quadrature_error_estimate':error})
    tails=[]
    for lam in [2.,5.,10.,25.,50.,100.]:
        sh=scaled_H(lam)
        tails.append({'lambda':lam,'scaled_H':sh,'lambda_times_correction':lam*(sh-1),'predicted_limit':1/24})
    # Independent scaled saddle quadrature inside the exact Palm integral.
    palm=[]
    for m in [2.,3.,4.,5.]:
        lam=1.;em=math.exp(m);hm=em
        def f(t):
            x=m+t/em;h=hm*math.exp(t/em)
            return (m/x)**2*math.exp(t/(2*em)-hm*math.expm1(t/em))*scaled_H(h)
        rat=quad(f,0,35,epsabs=5e-10,epsrel=5e-10,limit=150)[0]
        palm.append({'lambda':lam,'m':m,'exact_first_Palm_moment_over_asymptotic':rat})
    report={'status':'all finite assertions passed','exact':exact,'normal_form_checks':normal,'profiles':profiles,'coefficient_diagnostics':table,'cutoff_diagnostics':cuts,'large_lambda_diagnostics':tails,'Palm_diagnostics':palm,'environment':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'sympy':sp.__version__,'mpmath':mp.__version__},'limitations':['Floating-point diagnostics are not interval certificates.','Finite tests do not prove infinite-support or asymptotic theorems.','No Lean module was compiled.','The small omitted t>35 Palm integral is a numerical truncation.']}
    (out/'verification_results.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    for name,rows in [('coefficients',table),('cutoffs',cuts),('profiles',profiles),('Palm',palm)]:
        with (out/f'{name}.csv').open('w',newline='',encoding='utf-8') as f:
            writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
    print(f"Exact assertions passed: {exact['passed']}")
    print(f"High-precision normal-form cases: {len(normal)}")
    print(f"Coefficient cases: {len(table)}; cutoff cases: {len(cuts)}")
    for row in table:print('coefficient',row)
    for row in cuts:print('cutoff',row)
    for row in palm:print('Palm',row)
    print(f'Wrote {out / "verification_results.json"}')

if __name__=='__main__':main()
