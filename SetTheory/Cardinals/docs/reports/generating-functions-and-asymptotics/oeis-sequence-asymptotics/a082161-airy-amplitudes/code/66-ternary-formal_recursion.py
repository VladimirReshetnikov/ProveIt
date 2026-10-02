"""Exact polynomial–Airy formal recursion; symbolic checks only, not analytic estimates."""
import sympy as s
import json
x,a,e=s.symbols('x a e')
ORDER=7

def trunc(p,n=ORDER):return s.series(p,e,0,n+1).removeO().expand()
def der(pair):
 A,B=pair
 return (s.diff(A,x)+(x+a)*B,A+s.diff(B,x))
def shifted(pair,delta,n):
 out=[0,0];cur=pair;pw=s.Integer(1)
 for j in range(n+1):
  if j:cur=der(cur);pw=trunc(pw*delta,n)
  for z in range(2):out[z]+=pw*cur[z]/s.factorial(j)
 return [trunc(z,n) for z in out]

def invertK(P):
 P=s.Poly(s.expand(P),x)
 deg=P.degree()
 if deg<0:return s.Integer(0)
 rem=P.as_expr();B=s.Integer(0)
 for d in range(deg,-1,-1):
  b=s.expand(rem).coeff(x,d)/(2*d+1)
  term=b*x**d
  B+=term
  rem=s.expand(rem-(-s.diff(term,x,3)/2+2*(x+a)*s.diff(term,x)+term))
 assert s.expand(rem)==0
 return s.expand(B)

phis=[(s.Integer(1),s.Integer(0))]
scalars={0:s.Integer(3),2:3*a}
checks=[]
for m in range(1,5):
 n=m+2
 tau=trunc((1-e**3)**s.Rational(-1,3),n)
 U=trunc(2-6*(x*e**2-3*e**3)/(2+x*e**2-e**3),n)
 ds=[trunc((x+c*e)*tau-x,n) for c in [-1,2]]
 residual=[0,0]
 for h,pair in enumerate(phis):
  for c,delta in enumerate(ds):
   shifted_pair=shifted(pair,delta,n-h)
   mult=trunc(e**h*tau**h*(U if c==0 else 1),n)
   for z in range(2):residual[z]+=trunc(mult*shifted_pair[z],n)
  for ell,val in scalars.items():
   if ell+h<=n:
    for z in range(2):residual[z]-=val*e**(ell+h)*pair[z]
 R=[s.expand(z).coeff(e,n) for z in residual]
 P=-R[0]/3;Q=-R[1]/3
 B0=invertK(s.expand(P-s.diff(Q,x)/2))
 sm=s.simplify(-3*B0.subs(x,0))
 B=s.expand(B0+sm/3)
 A=s.integrate(s.expand((Q-s.diff(B,x,2))/2),x)
 A=s.expand(A-A.subs(x,0))
 phis.append((A,B));scalars[n]=sm
 assert B.subs(x,0)==0
 L=[s.diff(A,x,2)+2*(x+a)*s.diff(B,x)+B,2*s.diff(A,x)+s.diff(B,x,2)]
 assert s.expand(3*L[0]+R[0]-sm)==0
 assert s.expand(3*L[1]+R[1])==0
 checks.append({'m':m,'scalar_order':n,'scalar':str(sm),'A':str(A),'B':str(B),'equation_exact':True,'boundary_exact':True})
print(json.dumps({'normalization':'A_m(0)=B_m(0)=0','checks':checks},indent=2))
