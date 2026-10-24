"""Exact shortened cleared radical norms over any commutative ring.
No divisions or assumptions on the denominator are used.
"""

def cleared_norm3(x,a,b,C,d):
 z=x*x; G=d*(z+a-b)-C; U=d*d*a*z; V=d*b*C
 G2=G*G; H=G2+4*(U-V)
 return H*H-16*U*G2

def cleared_norm4(x,a,b,c,C,d):
 x2=x*x;d2=d*d;ab_sum=a+b
 q0=d*(x2+c-ab_sum)-C;q1=-2*d*x
 T=d2*a*b;R=d*C;z=64*T*R
 A0=q0*q0+c*q1*q1-4*(T+R*ab_sum)
 A1=2*q0*q1
 f0=A0*A0+c*A1*A1-z*(x2+c)
 f1=2*(A0*A1+z*x)
 return f0*f0-c*f1*f1

def cleared_norm5(x,a,b,c,d,C,delta):
 x2=x*x;cd=c*d;cpd=c+d;dsq=delta*delta;apb=a+b
 q0=delta*(x2+cpd-apb)-C
 q3=2*delta;q1=q3*x;q12=q1*q1;q32=q3*q3
 T=dsq*a*b;R=delta*C;z=64*T*R
 A0=q0*q0+cpd*q12+cd*q32-4*(T+R*apb)
 A1=2*q1*(q0+d*q3);A2=2*q1*(q0+c*q3);A3=2*(q0*q3+q12)
 f0=A0*A0+c*(A1*A1)+d*(A2*A2)+cd*(A3*A3)-z*(x2+cpd)
 zx=z*x
 f1=A0*A1+d*A2*A3-zx
 f2=A0*A2+c*A1*A3-zx
 f3=A0*A3+A1*A2-z
 g0=f0*f0+4*(cd*(f3*f3)-c*(f1*f1)-d*(f2*f2))
 h=f0*f3-2*f1*f2
 return g0*g0-16*cd*h*h
