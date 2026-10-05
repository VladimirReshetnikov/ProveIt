#!/usr/bin/env python3
"""Exact algebraic consistency checks, not a formal proof of asymptotic estimates."""
import json
from pathlib import Path
import sympy as s


def zero(name, expr):
    value = s.simplify(expr)
    if value != 0:
        raise RuntimeError(f"{name}: expected zero, got {value}")
    return name

passed=[]
K,U,T1,T2,v1=s.symbols('K U T1 T2 v1', positive=True)
C=K*U+T1
V=K*K*U+2*K*T1+T2+v1
passed.append(zero('Schur complement', U-C*C/V-(U*T2-T1*T1+U*v1)/V))
passed.append(zero('Regression center difference', C/V-1/K+(K*T1+T2+v1)/(K*V)))
th,j=s.symbols('theta j', real=True)
Q=U-C*C/V
passed.append(zero('Completed satellite variance', th*th*V-4*s.pi*j*th*C+4*s.pi**2*j*j*U-(V*(th-2*s.pi*j*C/V)**2+4*s.pi**2*j*j*Q)))
Uc,Cc,Vc=s.symbols('U C V', positive=True)
kRRS,kRSS,kSSS,bp=s.symbols('kRRS kRSS kSSS beta_prime')
beta=Cc/Vc
qt=-kRRS+2*Cc*kRSS/Vc-Cc**2*kSSS/Vc**2
residual_derivative=-kRRS+2*beta*kRSS-beta**2*kSSS-2*bp*(Cc-beta*Vc)
passed.append(zero('Conditional variance derivative and beta cancellation', qt-residual_derivative))
a,k=s.symbols('a k', positive=True)
t=a*s.log(k)/k
width=k/(a*(s.log(k)-1))
passed.append(zero('Saddle edge derivative', s.diff(t,k)+1/(k*width)))
lam=a*(s.log(k)-1)/k**s.Rational(1,3)
passed.append(zero('Critical parameter logarithmic derivative', s.diff(lam,k)/lam-(1/(s.log(k)-1)-s.Rational(1,3))/k))
x=s.symbols('x')
series=s.series(s.pi*x/s.sin(s.pi*x),x,0,4).removeO()
passed.append(zero('Logistic second moment', 2*series.coeff(x,2)-s.pi**2/3))
v=s.symbols('v', positive=True)
z=s.exp(v+1)
passed.append(zero('Lambert leading reversion parameterization', a*z*(s.log(z)-1)-a*s.E*v*s.exp(v)))
result={'status':'passed','scope':'Exact symbolic identities only; no certification of the asymptotic theorem or numerical coefficients.','checks':passed,'sympy_version':s.__version__}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'{len(passed)} exact algebraic checks passed; explicit exceptions remain enabled under python -O.')
