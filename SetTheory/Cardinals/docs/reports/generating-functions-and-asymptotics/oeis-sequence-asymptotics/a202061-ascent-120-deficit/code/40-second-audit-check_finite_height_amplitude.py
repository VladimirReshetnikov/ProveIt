#!/usr/bin/env python3
"""Independent exact check of the previously unaudited fixed-q amplitude."""
import sympy as s
z,u,x,T=s.symbols('z u x T')
p=z**3-5*z**2+6*z-1
rho=3*z**2-10*z+2
b=1-x
D=(b*(u-b)+x*T*(x-u))**2-4*x*T*(1-u)*b*u
Dz=s.diff(D,u).subs({x:rho,T:1/z,u:z})
# 4*pi*C_q^2 from direct quadratic/square-root transfer.
from_root=-z*Dz/(4*rho**2*(1/z)**2*(1-z)**2)
claimed=-16*z**2+55*z-10
num,den=s.fraction(s.cancel(from_root-claimed))
assert s.rem(num,p,z)==0
print('PASS: direct quadratic singularity gives C_q^2=(-16z^2+55z-10)/(4pi)')
# Verify the singularity itself directly, with differentiation done before substitution.
val=D.subs({x:rho,T:1/z,u:z})
num,den=s.fraction(s.cancel(val))
assert s.rem(num,p,z)==0
print('PASS: Delta(rho,z,1/z)=0 modulo the defining cubic')
z0=s.CRootOf(p,0)
r0=rho.subs(z,z0)
a0=s.sqrt(claimed.subs(z,z0))/(2*s.sqrt(s.pi))*r0/(z0*(1-r0))
m0=r0/((1-r0)*z0+r0)
c0=s.log((1-m0)/(2*a0))
print('C_q =',s.N(s.sqrt(claimed.subs(z,z0))/(2*s.sqrt(s.pi)),40))
print('m_* =',s.N(m0,40))
print('a_* =',s.N(a0,40))
print('c_* =',s.N(c0,40))
