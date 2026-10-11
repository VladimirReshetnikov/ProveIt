#!/usr/bin/env python3
"""Independent numerical and exact checks of the completed beta--Hurwitz formulas.

The numerical checks are diagnostics, not interval certificates.  Only Python,
mpmath and sympy are required.  The output is written beside this script.
"""
from pathlib import Path
import json
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
L = mp.log(2*mp.pi)
g = mp.euler
checks = []

def check(name, lhs, rhs, tol=mp.mpf('1e-40')):
    err = abs(lhs-rhs)
    checks.append(dict(name=name, lhs=mp.nstr(lhs,55), rhs=mp.nstr(rhs,55),
                       absolute_error=mp.nstr(err,8), tolerance=mp.nstr(tol,4),
                       passed=bool(err < tol)))
    print(name, mp.nstr(err,8), flush=True)
    if not err < tol:
        raise AssertionError(name)

def weight(x, lam):
    return (mp.sinpi(x)/mp.pi)**(2*lam)

def cmean(lam):
    return mp.gamma(1+2*lam)/mp.gamma(1+lam)**2/(2*mp.pi)**(2*lam)

def A_integer(s, m):
    d = mp.fsum((-1)**n * mp.binomial(2*m,m+n)*n**(s-1)
                for n in range(1,m+1))/(2*mp.pi)**(2*m)
    return 2*mp.gamma(1-s)*(2*mp.pi)**(s-1)*mp.sinpi(s/2)*d

for m in (1,2,3):
    s=mp.mpf('-0.7')+mp.mpf('0.2')*1j
    direct=mp.quad(lambda x: weight(x,m)*mp.zeta(s,x),[0,mp.mpf('.5'),1])
    check('integer beta Fourier m='+str(m),direct,A_integer(s,m))

lam=mp.mpf('-0.25'); s=mp.mpf('-0.5')
direct=mp.quad(lambda x: weight(x,lam)*mp.zeta(s,x),[0,mp.mpf('.5'),1])
euler=mp.quad(lambda t:t**(-lam-1)*(1-t)**(2*lam)*mp.polylog(1-s,t),
              [0,mp.mpf('.5'),1])
rhs=-2*mp.gamma(1-s)*(2*mp.pi)**(s-1-2*lam)*mp.sinpi(s/2)*mp.sinpi(lam)/mp.pi*euler
check('nonintegral polylog Euler transform',direct,rhs,mp.mpf('1e-28'))

for lam in (mp.mpf('.5'),mp.mpf('1.2'),mp.mpf('2.3')):
    direct=mp.quad(lambda x: weight(x,lam)*mp.loggamma(x),[0,mp.mpf('.5'),1])
    check('Gamma primitive lambda='+str(lam),direct,-mp.diff(cmean,lam)/4)

def gamma0_log_moment(k):
    def integrand(x):
        lx=mp.log(x)
        d=mp.log(mp.sinc(mp.pi*x))
        local=mp.fsum(mp.binomial(k,j)*lx**(k-j)*d**j/x for j in range(1,k+1))
        return local-mp.digamma(1+x)*(lx+d)**k
    return mp.quad(integrand,[0,mp.mpf('.25'),mp.mpf('.75'),1])

z2=mp.zeta(2); z3=mp.zeta(3)
zprime2=mp.diff(mp.zeta,2)
zsecond0=mp.diff(mp.zeta,0,2)
M1=gamma0_log_moment(1)
check('first logarithmic Stieltjes moment',M1,zsecond0+z2/2)

# D'(1) from a finite digamma sum and independent Stirling/Hurwitz tail.
N=40; K=30
Dp=mp.fsum(-(mp.digamma(n)-mp.log(n))*mp.log(n)/n for n in range(1,N))
Dp-=mp.diff(lambda z:mp.zeta(z,N),2)/2
Dp-=mp.fsum(mp.bernoulli(2*k)/(2*k)*mp.diff(lambda z:mp.zeta(z,N),2*k+1)
             for k in range(1,K+1))
eta=Dp-g*mp.stieltjes(1)-mp.stieltjes(2)
gammaH1=-eta-zprime2
M2=gamma0_log_moment(2)
M2_rhs=(-2*gammaH1-zprime2-2*L*mp.stieltjes(1)-g**3/3-g*g*L
        +2*L**3/3-2*z3/3)
check('second logarithmic harmonic bridge',M2,M2_rhs)

# Independent finite-part quadrature of psi^3 by local Laurent subtraction.
b=mp.mpf('.25'); degree=120
coeff={-1:mp.mpf(-1),0:-g}
coeff.update({j:(-1)**(j+1)*mp.zeta(j+1) for j in range(1,degree+3)})
square={}
for i,ci in coeff.items():
    for j,cj in coeff.items():
        if i+j<=degree+1: square[i+j]=square.get(i+j,0)+ci*cj
cube={}
for i,ci in square.items():
    for j,cj in coeff.items():
        if i+j<=degree: cube[i+j]=cube.get(i+j,0)+ci*cj
local=mp.fsum(c*(mp.log(b) if j==-1 else b**(j+1)/(j+1)) for j,c in cube.items())
Q=local+mp.quad(lambda x:mp.digamma(x)**3,[b,1])
check('incoming cubic bridge cross-check',Q,3*z2-6*eta-6*g*mp.stieltjes(1))
combo=3*z2+3*zprime2-6*(g+L)*mp.stieltjes(1)-g**3-3*g*g*L+2*L**3-2*z3
check('new cubic minus log-sine-square identity',Q+3*M2,combo)

# Exact coefficient checks: normalized Fourier coefficient recurrence.
u=sp.Symbol('u')
for n in (1,2,4,7):
    r=-u/sp.Integer(n)
    for j in range(1,n): r*=1-u/sp.Integer(j)
    for j in range(1,n+1): r/=1+u/sp.Integer(j)
    E=sp.exp(-2*sp.Symbol('L')*u+sp.zeta(2)*u*u)
    actual=sp.series(E*r,u,0,3).removeO()
    expected=-u/n+u*u*(2*(sp.Symbol('L')+sp.harmonic(n))/n-sp.Rational(1,n*n))
    assert sp.expand(actual-expected)==0
    checks.append(dict(name='exact Fourier coefficient n='+str(n),passed=True))

out=dict(working_precision=mp.mp.dps,numerical_status='floating-point diagnostics, not interval certification',
         eta=mp.nstr(eta,55), gammaH1=mp.nstr(gammaH1,55), Q=mp.nstr(Q,55),
         psi_log_squared=mp.nstr(-M2,55),checks=checks,all_passed=all(c['passed'] for c in checks))
Path(__file__).with_name('beta_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('ALL BETA CHECKS PASSED',flush=True)
