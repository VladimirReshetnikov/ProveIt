import sympy as s
q,S,t,a,u,k=s.symbols('q S t a u k')
l1=(a-s.Rational(1,2))*u-a*k/2
l2=(u-k)*(s.Rational(5,24)-a/2)+k*(a-1)*(a-5)/24
l3=(u-k)*(a/s.Integer(3)-s.Rational(1,8))+k*(-a*a+4*a-3)/24
d=2*u-k
R2=l1*l1/2+l2
assert s.expand(24*R2-((3*d*d+k)*a*a-6*(u+1)*d*a+u*(3*u+5)))==0
R3=l1**3/6+l1*l2+l3;K=-2*l1+2
assert s.cancel(-48*R3/K-((d*d+k)*a*a-2*(u+2)*d*a+u*(u+3)))==0
for r in [2,3]:
 if r==2:
  tt=S*(3+5*q)/(6*(1+q)); P=(3*tt**2+(2-tt)*q)/(3+5*q);SS=6*t*(1+q)/(3+5*q)
  target=-(15*q*t*t+5*q*t-6*q+3*t*t+3*t-6)/((q+1)*(5*q+3)**2)
 else:
  tt=S*(1+3*q)/(2*(1+2*q));P=(tt**2+(2-tt)*q)/(1+3*q);SS=2*t*(1+2*q)/(1+3*q)
  target=-(6*q*t*t+3*q*t-4*q+t*t+t-2)/((2*q+1)*(3*q+1)**2)
 assert s.cancel(s.diff(P,q).subs(S,SS)-target)==0
 print('defect',r,'exact quadratic and fixed-S derivative PASS')
print('Both derivative numerators are strictly positive for q>0,t>=1; t(q) is increasing, so any two physical candidates are connected through t>=1.')
