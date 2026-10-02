#!/usr/bin/env python3
"""Independent algebra/numerics for the one-sided next-constant proof.
These checks supplement, and do not certify, the analytic uniform estimates.
"""
import sympy as S
z,u,x,T=S.symbols('z u x T')
poly=z**3-5*z**2+6*z-1
rho=3*z*z-10*z+2
alpha=(8*z*z-29*z+9)/7
v=(2*z*z-7*z+2)/2
b=1-x
B=b*(u-b)+x*T*(x-u)
Delta=B**2-4*x*T*(1-u)*b*u
subs={x:rho,T:1/z,u:z}
def zero_mod(expr):
    num,den=S.fraction(S.cancel(expr))
    assert S.rem(num,poly,z)==0
    assert S.rem(den,poly,z)!=0
zero_mod(Delta.subs(subs))
print('PASS: critical discriminant vanishes modulo cubic')
amp2=-z*S.diff(Delta,u).subs(subs)/(4*rho**2*(1/z)**2*(1-z)**2)
zero_mod(amp2-(-16*z*z+55*z-10))
print('PASS: 4*pi*C_q^2 equals -16*z^2+55*z-10')
raw_mass=-B.subs(subs)/(2*(1-rho)*(1-z))
m=rho/((1-rho)*z+rho)
zero_mod(raw_mass-m)
print('PASS: exact unrestricted critical row mass')
z0=S.CRootOf(poly,0)
a=S.sqrt(-16*z*z+55*z-10)/(2*S.sqrt(S.pi))*rho/((1-rho)*z)
cstar=S.log((1-m)/(2*a))
Y=(2*v*alpha/(3*S.pi**2))**S.Rational(1,3)
C=alpha/Y
kappa=S.log(Y)-2*S.log(3)+2*cstar
for name,value in [('z',z),('alpha',alpha),('v',v),('m_star',m),('a_star',a),('c_star',cstar),('Y_0',Y),('C',C),('kappa',kappa)]:
    print(name,'=',S.N(value.subs(z,z0),45))
B0,Y0,alpha0,eps,ell,c,d=S.symbols('B0 Y0 alpha eps ell c d',positive=True)
# C(B)=3B/Y(B), Y(B)=Y0*(B/B0)^(1/3), B0=alpha/3.
Bvar=S.symbols('Bvar',positive=True)
CofB=3*Bvar/(Y0*(Bvar/B0)**S.Rational(1,3))
assert S.simplify(S.diff(CofB,Bvar).subs(Bvar,B0)-2/Y0)==0
print("PASS: C'(B0)=2/Y0")
log_constant=S.expand_log(2*S.log(S.Rational(2,3))-2*S.log(2),force=True)
assert S.simplify(log_constant+2*S.log(3))==0
print('PASS: logarithmic constants combine to -2*log(3)')
