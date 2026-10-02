"""Independent exact replay; does not import the main package checkers."""
import sympy as S
import json, hashlib
from pathlib import Path
if not __debug__:
 raise SystemExit("Run without -O: exact assertions are required")
OUTPUT = Path(__file__).resolve().parents[1] / "output" / "verification" / (Path(__file__).stem + ".json")
OUTPUT.parent.mkdir(parents=True, exist_ok=True)
x,a,e=S.symbols('x a e')
MAX=8
zero=(S.Integer(0),S.Integer(0))
def add(u,v):return (S.expand(u[0]+v[0]),S.expand(u[1]+v[1]))
def scale(u,c):return (S.expand(u[0]*c),S.expand(u[1]*c))
def diff(u):return (S.expand(S.diff(u[0],x)+2*(x+a)*u[1]),S.expand(u[0]+S.diff(u[1],x)))
def conv(u,v,n=MAX):
 w=[S.Integer(0)]*(n+1)
 for i,b in enumerate(u):
  for j,c in enumerate(v):
   if i+j<=n and b!=0 and c!=0:w[i+j]+=b*c
 return [S.expand(t) for t in w]
def power(u,k,n=MAX):
 w=[S.Integer(1)]+[S.Integer(0)]*n
 for _ in range(k):w=conv(w,u,n)
 return w
def binseries(q,n=MAX):
 w=[S.Integer(0)]*(n+1)
 for j in range(n//3+1):w[3*j]=S.rf(q,j)/S.factorial(j)
 return w
t=binseries(S.Rational(1,3))
one=[S.Integer(1)]+[S.Integer(0)]*MAX
bden=[S.Integer(1),0,x,-1]+[0]*(MAX-3)
invden=[S.Integer(1)]+[S.Integer(0)]*MAX
for n in range(1,MAX+1):invden[n]=S.expand(-sum(bden[k]*invden[n-k] for k in range(1,n+1)))
b=conv([1,0,-x,3]+[0]*(MAX-3),invden)
deltas={}
for sign in [-1,1]:
 d=[S.expand(x*c) for c in t];d[0]-=x
 for n in range(1,MAX+1):d[n]+=sign*t[n-1]
 deltas[sign]=[power(d,k) for k in range(MAX+1)]

def shifted(profile,k,sign):
 n=MAX-k
 out=[zero]*(MAX+1);dv=profile
 for r in range(n+1):
  for j,c in enumerate(deltas[sign][r]):
   if j<=n and c!=0:out[j]=add(out[j],scale(dv,c/S.factorial(r)))
  dv=diff(dv)
 bf=binseries(S.Rational(k,3))
 out2=[zero]*(MAX+1)
 for i,u in enumerate(out):
  if u==zero:continue
  for j,c in enumerate(bf):
   if i+j+k<=MAX and c!=0:out2[i+j+k]=add(out2[i+j+k],scale(u,c))
 return out2
G={0:(S.Integer(1),S.Integer(0))};sc={2:a}

def residual(n):
 out=[zero]*(MAX+1)
 for k,g in G.items():
  minus=shifted(g,k,-1);plus=shifted(g,k,1)
  for j in range(MAX+1):
   out[j]=add(out[j],plus[j])
   for q in range(j+1):
    if b[q]!=0:out[j]=add(out[j],scale(minus[j-q],b[q]))
  out[k]=add(out[k],scale(g,-2))
  for q,s in sc.items():
   if k+q<=MAX:out[k+q]=add(out[k+q],scale(g,-2*s))
 return out[n]

def invertT(rhs):
 rhs=S.Poly(S.expand(rhs),x);rem=rhs.as_expr();Q=S.Integer(0)
 for j in range(max(rhs.degree(),0),-1,-1):
  c=S.expand(rem).coeff(x,j)/S.Integer(4*j+2);term=c*x**j
  Q+=term
  T=-S.diff(term,x,3)/2+4*(x+a)*S.diff(term,x)+2*term
  rem=S.expand(rem-T)
 assert rem==0,rem
 return S.expand(Q)
assert residual(2)==zero
out={'s':{'2':str(a)},'profiles':{},'checks':[]}
for m in range(3,MAX+1):
 R,B=residual(m)
 Q0=invertT(-R+S.diff(B,x)/2)
 sm=S.expand(-Q0.subs(x,0));Q=S.expand(Q0+sm)
 P=S.integrate(S.expand((-B-S.diff(Q,x,2))/2),x)
 P=S.expand(P-P.subs(x,0)-S.diff(Q,x).subs(x,0))
 G[m-2]=(P,Q);sc[m]=sm
 chk=residual(m)
 assert chk==zero,(m,chk)
 assert Q.subs(x,0)==0 and S.expand(P.subs(x,0)+S.diff(Q,x).subs(x,0))==0
 # mod-3 weights for each polynomial monomial.
 assert all((da+m)%3==0 for (da,),coef in S.Poly(sm,a).terms() if coef)
 assert all((dx+da+m-2)%3==0 for (dx,da),coef in S.Poly(P,x,a).terms() if coef)
 assert all((dx+da+m-3)%3==0 for (dx,da),coef in S.Poly(Q,x,a).terms() if coef)
 out['s'][str(m)]=str(sm);out['profiles'][str(m-2)]={'P':str(P),'Q':str(Q)}
 out['checks'].append(f'order {m}: recurrence, boundary, derivative, grading all exact')
 print('m=',m,'s=',sm,flush=True)
# independently match log H ratio; N=e^-3.
hs=S.symbols('h1:4');logratio=3*a/e*(1-(1-e**3)**S.Rational(1,3))-S.Rational(4,3)*S.log(1-e**3)
for k,h in enumerate(hs,1):logratio+=h*e**k*(1-(1-e**3)**(-S.Rational(k,3)))
want=S.log(1+sum(sm*e**m for m,sm in sc.items()))
ld=S.series(logratio-want,e,0,7).removeO().expand()
sol=S.solve([ld.coeff(e,m) for m in range(4,7)],hs)
out['h']={str(h):str(S.factor(v)) for h,v in sol.items()}
# F normalized to F'(0)=1; independent ODE Taylor coefficients.
F=[S.Integer(0),S.Integer(1)]
for n in range(5):F.append(S.expand((2*a*F[n]+(2*F[n-1] if n else 0))/((n+2)*(n+1))))
Fe=sum(c*e**i for i,c in enumerate(F));Fpe=sum((i+1)*F[i+1]*e**i for i in range(len(F)-1))
endpoint=sum(e**k*(P.subs(x,e)*Fe+Q.subs(x,e)*Fpe) for k,(P,Q) in G.items())/e
endlog=S.series(S.log(S.series(endpoint,e,0,4).removeO()),e,0,4).removeO()
logcor=S.expand(sum(sol[h]*e**k for k,h in enumerate(hs,1))+endlog)
z,tv=S.symbols('z tv');nlog=S.expand(logcor.subs({a:z/2**S.Rational(1,3),e:tv/2**S.Rational(1,3)}))
coeff=S.series(S.exp(nlog),tv,0,4).removeO().expand()
out['endpoint_log_N']={str(k):str(S.factor(logcor.coeff(e,k))) for k in range(1,4)}
out['endpoint_log_n']={str(k):str(S.factor(nlog.coeff(tv,k))) for k in range(1,4)}
out['c_n']={str(k):str(S.factor(coeff.coeff(tv,k))) for k in range(1,4)}
expected_s={2:a,3:S.Rational(4,3),4:29*a*a/270,5:-23*a/81,6:(74385-8783*a**3)/85050}
assert all(S.expand(sc[k]-v)==0 for k,v in expected_s.items())
expected_c={1:53*z*z/90,2:z*(2809*z**3+26400)/16200,3:(1042139*z**6+28444320*z**3+30836700)/30618000}
assert all(S.expand(coeff.coeff(tv,k)-v)==0 for k,v in expected_c.items())
path=OUTPUT;path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['h','endpoint_log_N','endpoint_log_n','c_n']},indent=2))
