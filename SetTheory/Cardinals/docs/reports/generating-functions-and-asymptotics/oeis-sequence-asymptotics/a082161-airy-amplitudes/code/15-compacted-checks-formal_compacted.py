from pathlib import Path
"""Exact symbolic Airy coefficients for the compacted signed-delay recurrence."""
import sympy as s
import json
x,e,a=s.symbols('x e a'); V=2*(x+a)
def add(u,v): return tuple(s.expand(u[i]+v[i]) for i in (0,1))
def mul(c,u): return tuple(s.expand(c*p) for p in u)
def D(u): return (s.expand(s.diff(u[0],x)+V*u[1]),s.expand(u[0]+s.diff(u[1],x)))
def trunc(f,N): return s.series(f,e,0,N+1).removeO().expand()
def shift(u,y,N):
 delta=trunc(y-x,N); ans=(0,0); du=u
 for i in range(N+1):
  ans=add(ans,mul(trunc(delta**i/s.factorial(i),N),du));du=D(du)
 return tuple(trunc(p,N) for p in ans)
def poly_solve(R,S):
 # Solve L(PF+QF')=RF+SF' using descending degrees.
 T=s.expand(R-s.diff(S,x)/2); Q=0
 while T!=0:
  deg=s.degree(T,x); c=s.expand(T).coeff(x,deg)/(4*deg+2)
  term=c*x**deg; Q+=term
  T=s.expand(T-(-s.diff(term,x,3)/2+4*(x+a)*s.diff(term,x)+2*term))
 P=s.integrate((S-s.diff(Q,x,2))/2,x)
 P=s.expand(P-P.subs(x,0)-s.diff(Q,x).subs(x,0))
 return (P,s.expand(Q))
MAX=6
u=trunc((1-x*e**2+3*e**3)/(1+x*e**2-e**3),MAX)
beta=trunc(2*e**3*(1-x*e**2-e**3)/((1+x*e**2-e**3)*(1+x*e**2-3*e**3)),MAX)
ym=trunc((x-e)*(1-e**3)**(-s.Rational(1,3)),MAX)
yp=trunc((x+e)*(1-e**3)**(-s.Rational(1,3)),MAX)
y3=trunc((x-e)*(1-3*e**3)**(-s.Rational(1,3)),MAX)
Fs=[(s.Integer(1),s.Integer(0))]; ss={2:a}
for m in range(3,MAX+1):
 ratio_prev=[]
 for r in (1,2):
  ratio_prev.append(2*(1+sum(v*e**j*trunc((1-r*e**3)**(-s.Rational(j,3)),m-j) for j,v in ss.items() if j<=m)))
 back=trunc(1/(ratio_prev[0]*ratio_prev[1]),m-3)
 rhs=(0,0)
 for k,F in enumerate(Fs):
  inside=add(mul(u,shift(F,ym,m-k)),shift(F,yp,m-k))
  rhs=add(rhs,mul(e**k*trunc((1-e**3)**(-s.Rational(k,3)),m-k),inside))
  if k+3<=m:
   rhs=add(rhs,mul(-beta*back*e**k*trunc((1-3*e**3)**(-s.Rational(k,3)),m-k-3),shift(F,y3,m-k-3)))
 lhs=mul(2*(1+sum(v*e**j for j,v in ss.items())),tuple(sum(e**k*F[i] for k,F in enumerate(Fs)) for i in (0,1)))
 res=add(rhs,mul(-1,lhs)); R,S=[s.expand(p).coeff(e,m) for p in res]
 # New equation L(G)-2*s_m*F+R*F+S*F'=0.
 P,Q=poly_solve(-R,-S)
 sm=-Q.subs(x,0) # adding 2*s_m to forcing adds s_m to Q
 ss[m]=s.factor(sm);Q=s.expand(Q+sm)
 P=s.expand(P-P.subs(x,0)-s.diff(Q,x).subs(x,0))
 Fs.append((s.factor(P),s.factor(Q)))
 print('m',m,'s=',ss[m],'G=',Fs[-1],flush=True)
# log H and endpoint conversion.
h=s.symbols('h1:4');rho=ss[3]
logratio=3*a/e*(1-(1-e**3)**s.Rational(1,3))-rho*s.log(1-e**3)+sum(h[j-1]*e**j*(1-(1-e**3)**(-s.Rational(j,3))) for j in range(1,4))
target=trunc(s.log(1+sum(v*e**k for k,v in ss.items())),6)
sol=s.solve([trunc(logratio-target,6).coeff(e,k) for k in range(4,7)],h,dict=True)[0]
print('logH',sol)
f=[s.Integer(0),s.Integer(1)]
for k in range(2,10): f.append(s.expand(2*(a*f[k-2]+(f[k-3] if k>=3 else 0))/(k*(k-1))))
F=sum(c*x**i for i,c in enumerate(f));Fp=s.diff(F,x)
end=trunc(sum(e**k*(P*F+Q*Fp).subs(x,e) for k,(P,Q) in enumerate(Fs))/e,3)
print('endpoint',end)
logend=trunc(s.log(end),3)
logs=[s.factor(sol[h[k-1]]+logend.coeff(e,k)) for k in range(1,4)]
print('logforward_time',logs)
z=s.symbols('z');logs_n=[s.simplify(c.subs(a,z/2**s.Rational(1,3))/2**s.Rational(k,3)) for k,c in enumerate(logs,1)]
print('logforward_n',logs_n)
rel=trunc(s.exp(sum(c*e**k for k,c in enumerate(logs_n,1))),3)
print('relative_n',[s.factor(rel.coeff(e,k)) for k in range(1,4)])
open(Path(__file__).with_name('formal-coefficients.json'),'w').write(json.dumps({'s':{str(k):str(v) for k,v in ss.items()},'profiles':[[str(p),str(q)] for p,q in Fs],'logH':{str(k):str(v) for k,v in sol.items()},'logforward_n':list(map(str,logs_n))},indent=2))
