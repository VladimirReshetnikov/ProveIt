import sympy as s
x,L,q,e=s.symbols('x L q e', nonzero=True)
k=q+1
N=4
tr=lambda z,n=N:s.series(z,e,0,n+1).removeO().expand()
def der(v):
 A,B=v
 return [s.diff(A,x)+2*(x+L)*B/q,A+s.diff(B,x)]
def shift(v,delta,n):
 out=[0,0];pw=1
 for j in range(n+1):
  if j: v=der(v);pw=tr(pw*delta,n)
  for z in range(2):out[z]+=pw*v[z]/s.factorial(j)
 return [tr(z,n) for z in out]
phi=[(s.Integer(1),s.Integer(0)),(-(q+3)*x*x/(6*q)-(q-1)*L*x/(3*q),s.Integer(0))]
tau=tr((1-e**3)**s.Rational(-1,3))
U=tr(q*q*(1-x*e**2+(k+1)*e**3)/(q+x*e**2-e**3))
res=[0,0]
sc={0:k,2:k*L,3:k*(7*k-6)/6}
for h,v in enumerate(phi):
 for coeff,jump in [(U,-1),(s.Integer(1),q)]:
  w=shift(v,tr((x+jump*e)*tau-x),N-h)
  mult=tr(e**h*tau**h*coeff)
  for z in range(2):res[z]+=tr(mult*w[z])
 for order,val in sc.items():
  for z in range(2):res[z]-=val*e**(order+h)*v[z]
R=[s.factor(z.coeff(e,4)) for z in res]
P=-R[0]/k;Q=-R[1]/k
rem=s.expand(P-s.diff(Q,x)/2);B=0
for d in range(s.degree(rem,x),-1,-1):
 term=s.factor(s.expand(rem).coeff(x,d)/(2*d+1))*x**d
 B+=term
 rem=s.expand(rem-(-q*s.diff(term,x,3)/4+2*(x+L)*s.diff(term,x)+term))
assert s.simplify(rem)==0
s4=s.factor(-k*B.subs(x,0));B=s.expand(B+s4/k)
A=s.integrate(Q/q-s.diff(B,x,2)/2,x);A=s.factor(A-A.subs(x,0))
assert s.simplify(k*((q/2)*s.diff(A,x,2)+2*(x+L)*s.diff(B,x)+B)+R[0]-s4)==0
assert s.simplify(k*(q*s.diff(A,x)+(q/2)*s.diff(B,x,2))+R[1])==0
# log H_i/H_(i-1) e4 coefficient = -h1/3, and log scalar/k gives s4/k-L**2/2
h1=s.factor(-3*(s4/k-L**2/2))
print('s4 =',s4)
print('h1 =',h1)
print('phi2 A =',s.factor(A));print('phi2 B =',s.factor(B))
print('ternary s4:',s4.subs(q,2),' h1:',h1.subs(q,2))
# Next stage: phi3 and scalar s5, needed for c2.
phi.append((A,B));sc[4]=s4
N=5
tr=lambda z,n=N:s.series(z,e,0,n+1).removeO().expand()
tau=tr((1-e**3)**s.Rational(-1,3))
U=tr(q*q*(1-x*e**2+(k+1)*e**3)/(q+x*e**2-e**3))
res=[0,0]
for h,v in enumerate(phi):
 for coeff,jump in [(U,-1),(s.Integer(1),q)]:
  w=shift(v,tr((x+jump*e)*tau-x),N-h)
  mult=tr(e**h*tau**h*coeff)
  for z in range(2):res[z]+=tr(mult*w[z])
 for order,val in sc.items():
  for z in range(2):res[z]-=val*e**(order+h)*v[z]
R=[s.factor(z.coeff(e,5)) for z in res]
P=-R[0]/k;Q=-R[1]/k
rem=s.expand(P-s.diff(Q,x)/2);BB=0
for d in range(s.degree(rem,x),-1,-1):
 term=s.factor(s.expand(rem).coeff(x,d)/(2*d+1))*x**d
 BB+=term
 rem=s.expand(rem-(-q*s.diff(term,x,3)/4+2*(x+L)*s.diff(term,x)+term))
assert s.simplify(rem)==0
s5=s.factor(-k*BB.subs(x,0));BB=s.expand(BB+s5/k)
AA=s.integrate(Q/q-s.diff(BB,x,2)/2,x);AA=s.factor(AA-AA.subs(x,0))
assert s.simplify(k*((q/2)*s.diff(AA,x,2)+2*(x+L)*s.diff(BB,x)+BB)+R[0]-s5)==0
assert s.simplify(k*(q*s.diff(AA,x)+(q/2)*s.diff(BB,x,2))+R[1])==0
# log scalar: e5 coefficient=s5/k - L*beta.
# log G_i/G_(i-1): e5 coefficient=L/3.
# h2 contribution = -2*h2/3 e5.
beta=(7*q+1)/6
h2=s.factor(s.Rational(3,2)*(L/3-s5/k+L*beta))
# endpoint e2: f'''(0)/(6 f'(0)) + p'(0) + phi2'(0)/f'(0)
# f'''(0)=2L/q f'(0); phi2'(0)/f'(0)=B2'(0) since A2(0)=0.
e2=s.factor(L/(3*q)+s.diff(phi[1][0],x).subs(x,0)+s.diff(B,x).subs(x,0))
raw_c2=s.factor(h2+h1**2/2+e2)
print('s5 =',s5)
print('h2 =',h2)
print('endpoint e2 =',e2)
print('raw endpoint c2 =',raw_c2)
print('physical c2 = k^(-2/3) times raw endpoint c2')
print('ternary raw c2:',s.factor(raw_c2.subs(q,2)))
print('binary raw c2:',s.factor(raw_c2.subs(q,1)))
