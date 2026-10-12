#!/usr/bin/env python3
"""Exact independent checks of the collision proof's highest-risk constants.

The locally uniform analytic argument is audited in collision_audit.md.
These symbolic identities check its finite-part signs and displayed examples;
they are not substitutes for that argument or numerical error enclosures.
"""
from pathlib import Path
import json
import sympy as s

u,v=s.symbols('u v')
gam,g1,g2,z2,z3,z3p=s.symbols('gamma gamma1 gamma2 zeta2 zeta3 zeta3prime')
lam,mu=s.symbols('lambda mu',positive=True)
w=u+v
Q=1+z2*u*v-z3*u*v*w
E=lambda a:1+z2*a*a
Z=lambda a:gam-g1*a+g2*a*a/2

# These polynomial jets suffice through linear total spectral degree.
T=s.cancel((w-Q*(u*E(v)+v*E(u)))/(u*v*w))
F=s.cancel(T+(Z(v)-Q*E(u)*Z(w))/u+(Z(u)-Q*E(v)*Z(w))/v)
f00=s.expand(F).coeff(u,0).coeff(v,0)
f10=-s.expand(F).coeff(u,1).coeff(v,0)
assert f00==2*g1-2*z2
assert f10==s.Rational(3,2)*g2+2*gam*z2-z3

# Raw differentiated Hurwitz product minus the two critical local integrals.
Z3=lambda a:z3+z3p*a
common=(1+w)*(2+w)*Q*Z3(w)
critical_u=(1+u)*(1+v)*(2+v)*Z3(v)
critical_v=(1+v)*(1+u)*(2+u)*Z3(u)
F11=s.cancel((common*E(u)-critical_u)/u
             +(common*E(v)-critical_v)/v)
f11=s.expand(F11).coeff(u,0).coeff(v,0)
assert f11==2*z3+4*z3p

R=s.symbols('R')
for r in range(1,9):
    left=sum(s.binomial(r,j)*(R-1)**j/s.Integer(j) for j in range(1,r+1))
    right=sum((R**j-1)/s.Integer(j) for j in range(1,r+1))
    assert s.expand(left-right)==0

D=(s.log(lam)-s.log(mu))/(lam-mu)
Dlam=((lam-mu)/lam-s.log(lam)+s.log(mu))/(lam-mu)**2
Dlam_mu=((lam-mu)*(1/lam+1/mu)-2*(s.log(lam)-s.log(mu)))/(lam-mu)**3
assert s.simplify(s.diff(D,lam)-Dlam)==0
assert s.simplify(s.diff(D,lam,mu)-Dlam_mu)==0
assert s.limit(D,mu,lam)==1/lam
assert s.limit(Dlam,mu,lam)==-1/(2*lam**2)
assert s.limit(Dlam_mu,mu,lam)==1/(3*lam**3)

k00=lambda a,b:-s.log(a)
k01=lambda a,b:s.log(a)+1-b/a
k10=lambda a,b:-s.log(a)**2/2
digamma=f00+gam*(k00(lam,mu)+k00(mu,lam))
ordered=z2-z2*(k01(lam,mu)+k00(mu,lam))
trigamma=f11+2*z3*(k01(lam,mu)+k01(mu,lam))
stieltjes=f10+gam*k10(lam,mu)+g1*k00(mu,lam)
assert s.expand(ordered-z2*(mu/lam+s.log(mu)-s.log(lam)))==0
assert s.expand(trigamma-(4*z3p+2*z3*(3+s.log(lam)+s.log(mu)-mu/lam-lam/mu)))==0
assert s.expand(stieltjes-(s.Rational(3,2)*g2+2*gam*z2-z3-gam*s.log(lam)**2/2-g1*s.log(mu)))==0

payload={
 'scope':'Exact independent finite-part and collision-constant audit',
 'sympy_version':s.__version__,
 'arithmetic':'Exact symbolic and rational arithmetic; no floating point',
 'F00_00':str(f00),'F10_00':str(f10),'F00_11':str(f11),
 'ratio_polynomial_orders_checked':list(range(1,9)),
 'beta_derivatives_and_diagonal_limits':'All exact checks passed',
 'collision_constants':{
     'digamma':str(digamma),'ordered_digamma_trigamma':str(s.expand(ordered)),
     'trigamma_square':str(s.expand(trigamma)),
     'first_Stieltjes':str(s.expand(stieltjes))},
 'result':'All checks passed. See collision_audit.md for analytic uniformity proof audit.'}
out=Path(__file__).resolve().parents[1]/'results'/'collision_audit_verification.json'
out.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps(payload,indent=2))
