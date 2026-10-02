#!/usr/bin/env python3
"""Exact algebra certificate for the A202062 report. Requires SymPy only.

Finite-word tests are deliberately separate. This script verifies rational
identities used by the formal proof; it does not infer a theorem by fitting.
"""
import sympy as s
x,u,v,p,q,g,y=s.symbols('x u v p q g y')
b=1-x; d=1/x+x-3
K=b*(1-u)*(v-u)+x*u*(b+x*v)*(v-u)-x*u*v*(1-u)
Q=p+q-d*p*q+b*p*q*(p+q+p*q)

def reducer(poly,var,parameters):
    field=s.QQ.frac_field(*parameters)
    modulus=s.Poly(poly,var,domain=field).monic()
    def reduce(expr):
        num,den=s.fraction(s.cancel(expr))
        nn=s.Poly(num,var,domain=field).rem(modulus)
        dd=s.Poly(den,var,domain=field).rem(modulus)
        return (nn*s.invert(dd,modulus)).rem(modulus).as_expr()
    return reduce

rk=reducer(K,v,(x,u))
C=(b+x*v)*(v-u)/(v*(1-u))
assert rk((1-b*u)*C-x*v)==0
w=v/(u*(b+x*v))
assert rk(x*v-x-b*(u-1)*(w-1))==0
# This proves the kernel transformation independently of a series expansion.
assert s.factor(K.subs({u:1+p,v:1+b*p*q/x})/Q-b*p)==0
rq=reducer(Q,q,(x,p))
R=lambda z:b*z*z-(d+1)*z-d/(b*z)+1/(b*z*z)
assert rq(R(p)-R(q)+b*(p-q)*p*q)==0
J=lambda z:(b*z*z-(x*x-x+1)/x*z+1/(x-b*z)
 +(4*x**4-6*x**3+5*x*x-2*x+1)/(2*b*x*x)
 -(x*x-x+1)/(x*x*(z+1))+b/(x*x*(z+1)**2)
 -d/(b*z)+1/(b*z*z))
assert rq(J(p)-J(q))==0
# The seven-cycle is a useful additional identity, although explicit J suffices.
p0,p1=p,q
for _ in range(7):p0,p1=p1,rq(1/(b*p0*(1+p1)))
assert rq(p0-p)==0 and rq(p1-q)==0
k=-(x*x-2*x+2)/x
assert s.factor(-x-R(-1)-k)==0
assert s.factor(x*x/b-R(x/b)-k)==0
assert s.factor(x+x/b-s.diff(R(p),p).subs(p,-1))==0
A=b*b*p**3+(x*x-1)*p*p+x*p+x
B=x*(x-1)*p**3+2*x*(x-1)*p*p+(x*x-3*x+1)*p-2*x
Ccrit=2*x*(x-1)*p**3+(5*x*x-5*x+1)*p*p+(4*x*x-2*x)*p+x*x
assert s.factor(s.diff(J(p),p)-A*B*Ccrit/(b*p**3*x*x*(p+1)**3*(x-b*p)**2))==0

field=s.QQ.frac_field(x); modulus=s.Poly(A,p,domain=field).monic()
red=lambda expr:s.Poly(expr,p,domain=field).rem(modulus)
inv=lambda expr:s.invert(s.Poly(expr,p,domain=field),modulus)
one=red(1); ivp=inv(p); iv1=inv(p+1)
Jmod=(red(b*p*p-(x*x-x+1)/x*p+(4*x**4-6*x**3+5*x*x-2*x+1)/(2*b*x*x))
 +inv(x-b*p)-(x*x-x+1)/x**2*iv1+b/x**2*(iv1*iv1).rem(modulus)
 -d/b*ivp+1/b*(ivp*ivp).rem(modulus)).rem(modulus)
s1=(1+x)/b; s2=s1*s1-2*x/(b*b)
trace=s.factor(3*Jmod.nth(0)+Jmod.nth(1)*s1+Jmod.nth(2)*s2)
T=-(23*x**4-26*x**3+3*x*x+6*x+5)/(4*x*x*(x-1))
assert s.factor(trace-T)==0
j0=(4*x**4-4*x**3+x*x+1)/(2*b*x*x)
GP=(one+(red(T)-Jmod)/(2*x)+(k-j0)/x*one).rem(modulus)
GN=(7*(x**3-2*x*x+2*x-1)*p*p+(8*x**3-16*x*x+6*x+8)*p+x**3+18*x*x-20*x-1)
assert (GP-red(GN/(8*x**3))).is_zero
P=(64*x**6*(x-1)**2*g**3
 +(-16*x**8-400*x**7+1136*x**6-1008*x**5+272*x**4+16*x**3)*g*g
 +(x**8+148*x**7+226*x**6-1952*x**5+2819*x**4-1512*x**3+298*x*x-28*x+1)*g
 -4*x**7-335*x**6+1419*x**5-2082*x**4+1249*x**3-272*x*x+27*x-1)
remainder=red(0)
for co in s.Poly(P,g).all_coeffs():remainder=(remainder*GP+red(co)).rem(modulus)
assert remainder.is_zero
assert P.subs(x,0)==g-1
Y=12*x**3*g-(x**4+26*x**3-45*x*x+18*x+1)/(x-1)
GK=(4*(x-1)**3*Y**3
 -3*(x-1)*(x*x-x+1)*(x**6-235*x**5+1430*x**4-1695*x**3+270*x*x+229*x+1)*Y
 +x**12+510*x**11-14631*x**10+80090*x**9-218058*x**8+316290*x**7
 -253239*x**6+131562*x**5-70998*x**4+37950*x**3-8955*x*x-522*x+1)
assert s.factor(GK-108*x**3*(x-1)*P)==0
D=x**3+5*x*x-8*x+1
assert s.factor(s.discriminant(A,p)+4*x*(x-1)**3*D)==0
tau=(8-17*x-3*x*x)/7
assert s.rem(s.together(A.subs(p,tau)).as_numer_denom()[0],D,x)==0
assert s.rem(s.together(s.diff(A,p).subs(p,tau)).as_numer_denom()[0],D,x)==0
print('PASS: all exact kernel, invariant, branch-polynomial, trace, parameter, cubic, source-comparison, and discriminant identities')
