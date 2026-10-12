#!/usr/bin/env python3
"""Reproducible floating-point diagnostics; not interval certificates.

Normal-form evaluation and direct mpmath polylogarithm evaluation are compared.
The analytic error and convergence statements are proved in the article.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--dps',type=int,default=180)
args=parser.parse_args()
if args.dps < 180:
    raise SystemExit('Use at least 180 digits for the supplied fixed residual tolerances; direct subtraction is ill-conditioned here.')
mp.mp.dps=args.dps
checks=[]
rows=[]
def text(z): return mp.nstr(z,45)
def record(name,value,tol=mp.mpf('1e-45')):
    tol=mp.mpf(tol)
    value=abs(value)
    passed=bool(mp.isfinite(value) and value<tol)
    checks.append({'name':name,'absolute_or_scaled_error':text(value),'tolerance':text(tol),'passed':passed})
    if not passed: raise AssertionError(f'{name}: {value} >= {tol}')

class NormalForm:
    def __init__(self,n:int,e,terms:int=36):
        self.n=n;self.e=mp.mpc(e);self.terms=terms
        self.logg=mp.loggamma(1-self.e)-mp.fsum(mp.log1p(self.e/j) for j in range(1,n+1))
        self.Z=mp.euler if not self.e else mp.zeta(1+self.e)-1/self.e
        self.zeta1=None if not self.e else self.Z+1/self.e
        self.coeff=[(-1)**(j+1)*mp.factorial(n)*mp.zeta(self.e-j)/mp.factorial(n+j+1) for j in range(terms)]
    def tail(self,t):
        return mp.polyval(list(reversed(self.coeff)),t)
    def tailprime(self,t):
        return mp.polyval(list(reversed([j*self.coeff[j] for j in range(1,self.terms)])),t) if self.terms>1 else mp.mpf(0)
    def block(self,t):
        return -mp.expm1(self.logg+self.e*mp.log(t))/self.e+self.Z if self.e else mp.harmonic(self.n)-mp.log(t)
    def forward(self,t):
        return t**self.n*(self.block(t)+t*self.tail(t))
    def direct(self,t):
        n=self.n;e=self.e
        sub=mp.fsum(mp.zeta(n+1+e-j)*(-t)**j/mp.factorial(j) for j in range(n))
        return (-1)**n*mp.factorial(n)*(mp.polylog(n+1+e,mp.exp(-t))-sub)
    def local(self,u,kappa=0,eta=0):
        b=-mp.expm1(self.logg+self.e*(mp.log(u)-kappa))/self.e+self.Z if self.e else mp.harmonic(self.n)+kappa-mp.log(u)
        return u**self.n*b+eta*u**(self.n+1)*self.tail(eta*u)-1
    def local_u(self,u,kappa=0,eta=0):
        n=self.n;e=self.e
        ex=mp.exp(self.logg+e*(mp.log(u)-kappa))
        b=-mp.expm1(self.logg+e*(mp.log(u)-kappa))/e+self.Z if e else mp.harmonic(n)+kappa-mp.log(u)
        return u**(n-1)*(n*b-ex)+eta*((n+1)*u**n*self.tail(eta*u)+eta*u**(n+1)*self.tailprime(eta*u))

# Normal form against independent direct evaluation, including integer order.
for n in [1,2,3]:
    for e in [mp.mpf(0),mp.mpf('0.08'),mp.mpc('-0.04','0.03')]:
        f=NormalForm(n,e,46)
        for t in [mp.mpf('.08'),mp.mpc('.04','.02')]:
            record(f'normal versus polylog n={n} e={e} t={t}',(f.forward(t)-f.direct(t))/f.forward(t),'1e-70')
print('Forward comparisons complete.',flush=True)

# Exact-order derivative: direct polylog parameter finite difference is NOT used;
# the displayed first jet is compared with a symmetric complex Cauchy coefficient.
# This is a numerical check of the independently evaluated family.
for n in [1,2]:
    t=mp.mpf('.11');radius=mp.mpf('.035');m=24
    jet=mp.mpc(0)
    for j in range(m):
        w=mp.exp(2j*mp.pi*j/m)
        e=radius*w
        f=NormalForm(n,e,1)
        jet += f.direct(t)/w
    jet/=m*radius
    a=mp.euler-mp.harmonic(n);b2=mp.zeta(2)+mp.fsum(mp.mpf(1)/j**2 for j in range(1,n+1))
    L=-mp.log(t)
    p=-mp.stieltjes(1)-((L-a)**2+b2)/2
    rt=mp.fsum((-1)**(j+1)*mp.factorial(n)*mp.diff(mp.zeta,-j)*t**j/mp.factorial(n+j+1) for j in range(36))
    record(f'first integer order jet n={n}',jet-(t**n*p+t**(n+1)*rt),'1e-29')
print('Order-jet comparisons complete.',flush=True)

# Primary crossover roots: logarithmic relative correction, uniform compact samples.
for n in [1,2,3]:
    for lam in [mp.mpf(-1),mp.mpf(0),mp.mpf(1)]:
        X=mp.mpf(28);e=lam/X;y=mp.exp(-n*X)
        A=-mp.expm1(-lam)/lam if lam else mp.mpf(1)
        tau=mp.exp(-X)/(X*A)**(mp.mpf(1)/n)
        f=NormalForm(n,e,12)
        correction=(mp.exp(-lam)*((mp.log(X)+mp.log(A))/n-(mp.euler-mp.harmonic(n)))+mp.euler)/(n*A*X)
        u=mp.findroot(lambda u:f.forward(tau*u)/y-1,(1-correction,1-correction+mp.mpf('.0001')),tol=mp.mpf('1e-115'))
        record(f'primary direct inverse n={n} lambda={lam}',f.direct(tau*u)/y-1,'1e-90')
        rows.append({'kind':'primary','n':n,'lambda':text(lam),'X':text(X),'U':text(u),'first_correction_error':text(abs(u-(1-correction)))})
print('Primary inverses complete.',flush=True)

# Closed core critical locus and its first full-tail variation, at several n.
for n in [1,2,3]:
    for e in [mp.mpf('.02'),mp.mpc(0,'.04')]:
        f=NormalForm(n,e,12)
        u0=mp.exp(mp.log((n+e)/(e*mp.zeta(1+e)))/n)
        k0=(f.logg-mp.log(n)+(n+e)*mp.log(u0))/e
        record(f'core critical value n={n} e={e}',f.local(u0,k0,0),'1e-150')
        record(f'core critical derivative n={n} e={e}',f.local_u(u0,k0,0),'1e-150')
        eta=mp.mpf('1e-5')
        k1=mp.zeta(e)*u0**(n+1)/(n*(n+1))
        u1=-(1-e)*mp.zeta(e)*u0**(n+2)/(n*(n+1)*(n+e))
        uc,kc=mp.findroot(lambda u,k:(f.local(u,k,eta),f.local_u(u,k,eta)),(u0+eta*u1,k0+eta*k1),tol=mp.mpf('1e-115'))
        record(f'full fold equation n={n} e={e}',f.local(uc,kc,eta),'1e-100')
        record(f'full fold derivative n={n} e={e}',f.local_u(uc,kc,eta),'1e-100')
        record(f'first tail motion n={n} e={e}',max(abs(uc-u0-eta*u1),abs(kc-k0-eta*k1))/eta**2,'1')
print('Core and full-fold diagnostics complete.',flush=True)

# Dilogarithm resonance: two actual roots, compared directly with polylogarithms.
a=mp.euler-1
K=mp.stieltjes(1)+(a*a+mp.zeta(2)+1)/2
b=-a-4*K/3
J0=mp.stieltjes(2)/2-a**3/6-a*(mp.zeta(2)+1)/2-(mp.zeta(3)-1)/3
M=a*a/2+(3*a+1)*K+13*K*K/9+J0
for k,X in [(1,80),(1,160),(1,320),(-1,160),(2,160)]:
    X=mp.mpf(X);lam=2*mp.pi*1j*k;e=lam/X;y=mp.exp(-X)
    f=NormalForm(1,e,6)
    for sign in [1,-1]:
        square=mp.sqrt(-2*K*e)
        approx2=1+sign*square+b*e
        approx3=approx2+sign*M*e*e/square
        u=mp.findroot(lambda u:f.local(u,0,y),(approx3,approx3+mp.mpf('.0001')),tol=mp.mpf('1e-115'))
        # At X=320 the cancellation costs about 139 decimal digits.
        direct_tol=mp.mpf('1e-32') if X>250 else mp.mpf('1e-85')
        record(f'secondary direct root k={k} X={X} sign={sign}',f.direct(y*u)/y-1,direct_tol)
        rows.append({'kind':'secondary','k':k,'X':text(X),'sign':sign,'U':text(u),'error_two_terms':text(abs(u-approx2)),'error_three_terms':text(abs(u-approx3)),'two_term_scaled_error':text(abs(u-approx2)*X**mp.mpf('1.5'))})
print('Secondary inverse diagnostics complete.',flush=True)

# Moving physical fold: solve in U and epsilon, with lambda=epsilon*X.
# Its order parameter differs from lambda_k at order X^-2.
for X in [mp.mpf(60),mp.mpf(120)]:
    lamk=2*mp.pi*1j;y=mp.exp(-X)
    lam0=lamk+K*lamk**2/X**2
    # Exact tail coefficients are recomputed for a changing epsilon; six terms
    # suffice here because y is exponentially small.
    def equations(u,lam):
        e=lam/X;f=NormalForm(1,e,3);kap=(lam-lamk)/e
        return f.local(u,kap,y),f.local_u(u,kap,y)
    uc,lc=mp.findroot(equations,(1-a*lamk/X,lam0),tol=mp.mpf('1e-95'))
    e=lc/X;f=NormalForm(1,e,4)
    record(f'physical fold value X={X}',f.direct(y*uc)/y-1,'1e-90')
    record(f'physical fold zero Li_(1+epsilon) X={X}',mp.polylog(1+e,mp.exp(-y*uc)),'1e-90')
    rows.append({'kind':'moving_fold','X':text(X),'lambda':text(lc),'shift':text(lc-lamk),'leading_shift_error_scaled':text(abs(lc-lam0)*X**3)})
print('Moving physical folds complete.',flush=True)

report={'mpmath_version':mp.__version__,'precision_dps':args.dps,'checks':checks,'comparisons':len(checks),'all_passed':all(c['passed'] for c in checks),'qualification':'Floating-point diagnostics only, not interval-certified final digits. No numerical check substitutes for an analytic proof.','constants':{'K':text(K),'b':text(b),'M':text(M)},'tables':rows}
ROOT.joinpath('results').mkdir(exist_ok=True)
ROOT.joinpath('results/numeric_checks.json').write_text(json.dumps(report,indent=2)+'\n')
# Short TeX table consumed by the manuscript.
sec=[r for r in rows if r['kind']=='secondary' and r['k']==1 and r['sign']==1]
with ROOT.joinpath('results/numeric_table.tex').open('w') as out:
    out.write(r'''\begin{tabular}{rrrr}
\toprule
$X$ & $|U_+-U^{(2)}|$ & $|U_+-U^{(3)}|$ & $X^{3/2}|U_+-U^{(2)}|$\\
\midrule
''')
    for row in sec:
        out.write(f"{int(mp.mpf(row['X']))} & {float(mp.mpf(row['error_two_terms'])):.6g} & {float(mp.mpf(row['error_three_terms'])):.6g} & {float(mp.mpf(row['two_term_scaled_error'])):.6g} \\\\\n")
    out.write('\\bottomrule\n\\end{tabular}\n')
print(f"{len(checks)} floating-point diagnostics passed at {args.dps} decimal digits.",flush=True)
