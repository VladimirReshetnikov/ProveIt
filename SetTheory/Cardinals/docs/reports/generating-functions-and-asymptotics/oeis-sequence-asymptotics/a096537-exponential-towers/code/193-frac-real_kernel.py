"""Outward-rounded evaluation of the reduced real integral core.
Depends on a separate mathematical proof of the real-integral identity and tail.
"""
from fractions import Fraction
from interval_decimal import I,D,DN,UP,NEAR,PI
from airy_interval import A,SQRT3,C,airy_range,atan_range
OMEGA=C(I(Fraction(-1,2)),SQRT3/2)
ROOT2=I(2).sqrt()
def kernel(z):
 z=I(z);t=z**2;ai,ap,bi,bp=airy_range(A*t)
 x=PI/A*ai*bi;r=ai/bi;y=PI/A*ai**2;p=C(x,y)
 v=2*A*ap/ai
 ar=atan_range(r)/r
 gv=I(Fraction(1,2))-t*v/2-v**3/12
 S=(gv*x-t-v**2/2-v/x*ar-2/(3*x**2*(1+r**2)))/A
 u=C(bp,ap)*(2*A)/C(bi,ai)
 gu=C(Fraction(1,2))-u*t/2-u**3/12
 ph=gu*p**2/2+(C(t)+u**2/2)*p-u*p.log_q1()-C(Fraction(2,3))/p
 num=ph.conj()*4-u.conj()*C(0,4*PI/3)-C(2*t**2)
 E=(OMEGA*num/C(ai,bi)**2).i/PI
 return 2*z*(E-S-2*t/(3*A))+ROOT2/A

