#!/usr/bin/env python3
"""Optional symbolic audit of the proof. Requires SymPy (tested with 1.14.0).
All assertions concern rational-function or polynomial identities, not numerical samples.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as S

z,a,b,c,d,u,v,s,L,k,W = S.symbols('z a b c d u v s L k W')
checks: list[str] = []

def check(name: str, expression: S.Expr) -> None:
    assert S.cancel(expression) == 0, name
    checks.append(name)

r = s-1
M = 1+s*z+L*z*z
D = M*M-4*k*z**3*(1+r*z)
I = v*v+(u*u+s*u+L)*v-k*(u+1)
L_on_curve = k*(u+1)/v-v-u*u-s*u

def on_curve(expression: S.Expr) -> S.Expr:
    return S.cancel(expression.subs(L,L_on_curve))

# 1. The displayed quartic really equals Barry's original coefficients.
delta = a*b*d-b*b*c+d*d
ss = a*b+2*d+2
LL = delta+ss-1
kk = b**4
AA = a*a*b*b*(d+1)**2-2*a*b*(2*b**4+b*b*c*(d+1)-(d+1)**3) \
     +b**4*(c*c-4*(2*d+1))-2*b*b*c*(d+1)**2+(d+1)**4
BB = 2*(a*a*b*b*(d+1)+a*b*(3*(d+1)**2-b*b*c) \
        -2*(b**4+b*b*c*(d+1)-(d+1)**3))
CC = a*a*b*b+6*a*b*(d+1)-2*(b*b*c-3*(d+1)**2)
check('Barry quartic coefficient A', LL**2-4*kk*(ss-1)-AA)
check('Barry quartic coefficient B', 2*ss*LL-4*kk-BB)
check('Barry quartic coefficient C', ss**2+2*LL-CC)
check('Barry radical denominator F', -(LL+2*kk)+(a*b*(d+1)+2*b**4-b*b*c+(d+1)**2))
check('Barry radical denominator G', 2*kk-ss-(2*(b**4-d-1)-a*b))

# 2. The elliptic curve becomes the invariant cubic under the stated substitution.
X = -v/b**2
Y = -v*(u+d+1)/b**3
E = Y*Y+a*X*Y+b*Y-X**3-c*X*X-d*X
check('birational invariant cubic', E*b**6/v-I.subs({s:ss,L:LL,k:kk}))

# 3. Exact rational map invariance and the complete-quotient factorization.
vp = -v-u*u-s*u-L
up = k/vp-s-u
gamma = k/v-u
N = 1+s*z+(L+2*v)*z*z
check('equivalent formulas for v next', on_curve(vp+k*(u+1)/v))
check('invariance of the cubic', on_curve(I.subs({u:up,v:vp}, simultaneous=True)))
check('complete quotient norm factorization',
      on_curve(N*N-D-4*v*z*z*(1+gamma*z)*(1+(s+u)*z)))
check('next linear denominator', k/vp-up-(s+u))
check('one-step numerator identity',
      2*(1-u*z)*(1+(s+u)*z)-N-W-(1+s*z+(L+2*vp)*z*z-W))

# 4. Initial tail: delta = L-s+1, u_2 = -(s-1)-k/delta, v_2=-delta.
del0 = L-s+1
u2 = -(s-1)-k/del0
v2 = -del0
check('initial pair lies on invariant cubic', I.subs({u:u2,v:v2}, simultaneous=True))
F2 = (1+s*z+(L+2*v2)*z*z-W)/(2*v2*z*z*(1+(k/v2-u2)*z))
check('initial q tail identity', 1+z+del0*z*z*F2-(M+W)/(2*(1+r*z)))
q = (M-W)/(2*k*z**3)
check('outer G expression', 1/(1-z-z*z*q)-2*k*z/(W+2*k*z*(1-z)-M))

# 5. Consecutive beta coefficients imply the Somos recurrence.
vm = k*(s+u-1)/v-k*k/v**2
check('QRT/Somos beta identity', on_curve(vm*v*v*vp-k*k*(v+L-s+1)))
v3 = vp.subs({u:u2,v:v2}, simultaneous=True)
check('initial Hankel h3', del0**2*v3+k*((s-2)*del0+k))

result = {'sympy_version':S.__version__, 'status':'ALL SYMBOLIC CHECKS PASSED',
          'checks':checks, 'check_count':len(checks)}
Path('data').mkdir(exist_ok=True)
Path('data/symbolic_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
