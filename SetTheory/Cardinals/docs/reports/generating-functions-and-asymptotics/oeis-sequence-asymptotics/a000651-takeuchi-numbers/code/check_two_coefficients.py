import sympy as s
w,k=s.symbols('w k')
d=w/(1+w);j=k+1
g=w**2/2-s.log(1+w)/2
p= -w**2*(26*w**2+67*w+46)/(24*(1+w)**3)
q,Q=s.symbols('q Q')
C=lambda x:s.cancel(x)
# derivative of F0, then g, ph, qh^2 via formal D=h*d*d/dw-h^2*d/dh
jets={0:w,1:C(d*s.diff(g,w)),2:C(d*s.diff(p,w)-p),3:d*Q-2*q}
logerr=[s.S(0)]*4
for t in range(1,5):
 for m,v in jets.items():
  if m<=3: logerr[m]+=(-j)**t/s.factorial(t)*v
 jets={m+1:C(d*s.diff(v,w)-m*v) for m,v in jets.items() if m<3}
logerr[0]+=j*w
logerr[1]+=k*(k-3)/2
logerr[2]+=-k*(2*k**2+3*k+1)/12
logerr[3]+=k**2*(k**2-6*k+1)/12
A=[s.Poly(s.cancel(x),k) for x in logerr[1:]]

def expect(poly):
 if not isinstance(poly,s.Poly):poly=s.Poly(poly,k)
 return s.factor(sum(c*s.bell(j[0],w) for j,c in poly.terms()))
R=[A[0],A[1]+A[0]**2/2,A[2]+A[0]*A[1]+A[0]**3/6]
for jj,x in enumerate(R,1):
 print('RESIDUAL',jj,expect(x),flush=True)
print('A1=',A[0].as_expr(),flush=True)
r3=expect(R[2]);P=C(r3.subs({q:0,Q:0}))
b=s.symbols('b0:7');trial=w**2*sum(b[i]*w**i for i in range(7))/(48*(1+w)**6)
eq=s.Poly(s.together(-w*s.diff(trial,w)+2*(w+1)*trial+P).as_numer_denom()[0],w)
sol=s.solve(eq.all_coeffs(),b);ans=s.factor(trial.subs(sol));print('q_solution=',ans,flush=True)
print('third residual after q=',s.factor(r3.subs({q:ans,Q:s.diff(ans,w)})),flush=True)
