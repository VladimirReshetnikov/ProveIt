"""Exact symbolic verification of P1; no second-correction claim or computation."""
import sympy as s
v,a,A,H,lam,x,g,E=s.symbols('v a A H lam x g E',positive=True)
R=a**4
# Critical expansions: d=a*t+a2*t²+a3*t³; rho=R+b2*t²+b3*t³+b4*t⁴.
a2,a3,b2,b3,b4=s.symbols('a2 a3 b2 b3 b4')
d=a*v+a2*v**2+a3*v**3;r=R+b2*v**2+b3*v**3+b4*v**4
char=s.series(d**4-r*v**4*(1-d),v,0,7).removeO().expand()
quart=s.series(d**4+(2*A*(r-R)+H*(r-R)**2)*d*d+r*v**4*(1-2*d+d*d/(2*R)),v,0,7).removeO().expand()
sol={a2:-a*a/4,b2:-a*a/A,b3:a**3/A}
sol[a3]=s.solve(char.coeff(v,6).subs(sol),a3)[0]
sol[b4]=s.factor(s.solve(quart.coeff(v,6).subs(sol),b4)[0])
f4=s.factor(-sol[b4]/R+sol[b2]**2/(2*R**2))
assert s.simplify(f4-(-1/(8*A)+1/(4*A*R)+H/(2*A**3)))==0
# The critical amplitude ratio through first order; rho*P_z/delta^2
# contributes its constant at this order, and P_delta_delta/delta^2=8+2delta/(1-delta).
amp=s.series(s.sqrt(8/(8+2*a*v/(1-a*v))),v,0,2).removeO()
assert s.expand(amp)==1-a*v/8
# Limiting physical root has no odd singular power beyond first.
xi=s.symbols('xi');V=(s.sqrt(4*a*a+g*g*xi*xi)+g*xi)/2
assert s.series(V,xi,0,6).removeO().coeff(xi,3)==0
# Gaussian computation with variance 2/lambda.
D=-2*g*lam**s.Rational(3,2)
z1=s.I*(3*D*x/4-lam*x**3/24)
z2=E*lam**2-9*D*x*x/32+lam*x**4/192
amp1=-g*s.sqrt(lam)/8
poly=s.Poly(s.expand(z2+z1*z1/2+amp1),x)
mean=sum(co*s.factorial2(j-1)*(2/lam)**(j//2) for (j,),co in poly.terms() if j%2==0)
P1=s.factor(mean+1/(24*lam))
assert s.simplify(P1-(g*s.sqrt(lam)/4+(E-9*g*g/4)*lam**2))==0
c=1/(a*a*A)
B=s.simplify((4*f4/c**2-9*g*g/4).subs(g*g,2*R*A))
expected=A*(1-5*R)+2*R*H/A
assert s.simplify(B-expected)==0
print('All exact symbolic assertions passed')
print('f4 =',f4)
print('P1(lambda) = gamma0*sqrt(lambda)/4 + B*lambda^2')
print('B =',s.factor(B))
print('The saddle 1/(24*lambda) term cancels against factorial normalization.')
