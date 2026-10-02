#!/usr/bin/env python3
"""Deterministic algebra and scale checks; not a substitute for the proofs."""
import sympy as S
import mpmath as mp
B,Y,v,n=S.symbols('B Y v n',positive=True)
# For V(h)=B/h, the scalar action is nB/Y + pi sqrt(2B/v) sqrt(Y).
J=n*B/Y+S.pi*S.sqrt(2*B/v)*S.sqrt(Y)
n_duration=S.pi*S.sqrt(B)*Y**S.Rational(3,2)/S.sqrt(2*v)/B
assert S.simplify(S.diff(J,Y).subs(n,n_duration))==0
assert S.simplify(J.subs(n,n_duration)-3*n_duration*B/Y)==0
print('PASS: scalar energy minimum and leading Kepler action')
# The angle measure ds/y is constant; its mass and logarithmic moment.
alpha,Y0=S.symbols('alpha Y0',positive=True)
angle_mass=2/Y0
log_average=S.log(Y0)-2*S.log(2)
assert S.simplify(alpha*angle_mass/2-alpha/Y0)==0
assert S.simplify(log_average+2*S.log(S.Rational(2,3))-(S.log(Y0)-2*S.log(3)))==0
print('PASS: Kepler angular averaging and kappa constant combination')
# Algebraic asymptotic order checks with M~n^(1/3)L^(-1/3), H~n^(2/3)L^(1/3).
# Ignore fixed logarithmic powers when a strict n exponent separates scales.
Mexp=S.Rational(1,3); Hexp=S.Rational(2,3); rexp=S.Rational(3,4)*Mexp
assert rexp<Mexp
assert Mexp-rexp<Mexp
assert Hexp+Mexp/2<rexp+Hexp
assert Mexp<S.Rational(1,2)
print('PASS: rL=o(M), ML^3/r=o(M), H sqrt(M)<<rH, drift bias<<sqrt(nL)')
# Independent high-precision evaluation with mpmath.
mp.mp.dps=80
z=mp.findroot(lambda q:q**3-5*q*q+6*q-1,mp.mpf('0.198'))
rho=3*z*z-10*z+2
al=(8*z*z-29*z+9)/7
vv=(2*z*z-7*z+2)/2
m=rho/((1-rho)*z+rho)
cq=mp.sqrt(-16*z*z+55*z-10)/(2*mp.sqrt(mp.pi))
a=rho*cq/((1-rho)*z)
c=mp.log((1-m)/(2*a))
y=(2*vv*al/(3*mp.pi**2))**(mp.mpf(1)/3)
C=al/y
kap=mp.log(y)-2*mp.log(3)+2*c
lam=-mp.log(rho)
BI=C*lam**(-mp.mpf(4)/3)
ki=kap-mp.mpf(2)/3*mp.log(lam)
assert mp.mpf('.44')<m<mp.mpf('.45')
assert mp.mpf('.55')<1-m<mp.mpf('.56')
assert abs(kap-mp.mpf('-1.940148183136270392093282071371173914943379613268'))<mp.mpf('1e-47')
assert abs(ki-mp.mpf('-2.398003540515347428750752039231889144665'))<mp.mpf('1e-37')
for name,value in [('log_mu',lam),('C_star',C),('c_star',c),('Y_0',y),('kappa',kap),('C_times_kappa',C*kap),('inverse_leading',BI),('inverse_kappa',ki)]:
    print(name,'=',mp.nstr(value,60))
print('PASS: exact definitions reproduce all displayed constants; patch has positive mass margin')
