import sympy as S
import json
from pathlib import Path
x,a,e=S.symbols('x a e')
N=7
zero=lambda:[S.Integer(0)]*(N+1)
def add(u,v):return [S.expand(p+q) for p,q in zip(u,v)]
def mul(u,v):return [S.expand(sum(u[j]*v[k-j] for j in range(k+1))) for k in range(N+1)]
def scale(u,v):return [S.expand(v*p) for p in u]
def power(u,k):
 v=zero();v[0]=1
 for _ in range(k):v=mul(v,u)
 return v
def deriv(pair):
 A,B=pair
 return (S.expand(S.diff(A,x)+(x+a)*B),S.expand(A+S.diff(B,x)))
def shift(pair,m,d):
 tau=zero()
 for k in range(N//3+1):tau[3*k]=S.rf(S.Rational(1,3),k)/S.factorial(k)
 delta=scale(tau,x);delta[0]-=x
 for k in range(N):delta[k+1]+=d*tau[k]
 ep=power(tau,m);ep=[0]*m+ep[:N+1-m]
 out=[zero(),zero()]; dp=pair
 for k in range(N-m+1):
  fac=scale(mul(ep,power(delta,k)),1/S.factorial(k))
  for z in range(2):out[z]=add(out[z],scale(fac,dp[z]))
  dp=deriv(dp)
 return out
U=[S.expand(S.series(2-6*(x*e**2-3*e**3)/(2+x*e**2-e**3),e,0,N+1).removeO()).coeff(e,k) for k in range(N+1)]
phi=[(S.Integer(1),S.Integer(0))]
ss={0:S.Integer(3),1:S.Integer(0),2:3*a}
results=[]
for m in range(1,N-1):
 k=m+2; res=[zero(),zero()]
 for l,pair in enumerate(phi):
  minus=shift(pair,l,-1);plus=shift(pair,l,2)
  for z in range(2):res[z]=add(res[z],add(mul(U,minus[z]),plus[z]))
  for si,sv in ss.items():
   if si+l<=N:
    for z in range(2):res[z][si+l]-=sv*pair[z]
 # 3 L phi_m + residual - s_new f = 0
 P=-S.expand(res[0][k])/3;Q=-S.expand(res[1][k])/3
 R=S.expand(P-S.diff(Q,x)/2)
 degree=S.degree(R,x); B=S.Integer(0)
 for d in range(max(0,degree),-1,-1):
  b=S.expand(R).coeff(x,d)/(2*d+1)
  mon=b*x**d;B+=mon
  R=S.expand(R-(-S.diff(mon,x,3)/2+2*(x+a)*S.diff(mon,x)+mon))
 sn=-3*B.subs(x,0);B=S.expand(B+sn/3)
 A=S.integrate(S.expand((Q-S.diff(B,x,2))/2),x);A=S.expand(A-A.subs(x,0))
 phi.append((A,B));ss[k]=S.expand(sn)
 lhs=deriv(deriv((A,B)));lhs=(S.expand(lhs[0]-(x+a)*A),S.expand(lhs[1]-(x+a)*B))
 assert S.expand(3*lhs[0]+res[0][k]-sn)==0
 assert S.expand(3*lhs[1]+res[1][k])==0
 results.append({'m':m,'s_'+str(k):str(S.factor(sn)),'A':str(S.factor(A)),'B':str(S.factor(B))})
 print(results[-1],flush=True)
Path(__file__).with_name('coefficients.json').write_text(json.dumps(results,indent=2))
sformal=sum(v*e**k for k,v in ss.items())
ls=S.series(S.log(sformal/3),e,0,N+1).removeO().expand()
base=S.series(3*a/e*(1-(1-e**3)**S.Rational(1,3))-S.Rational(5,2)*S.log(1-e**3),e,0,N+1).removeO().expand()
h={}
for r in range(1,N-2):
 coef=S.expand(ls-base).coeff(e,r+3)
 h[r]=S.factor(-3*coef/r)
 base+=S.series(h[r]*e**r*(1-(1-e**3)**(-S.Rational(r,3))),e,0,N+1).removeO().expand()
assert S.expand(ls-base)==0
fc=[S.Integer(0),S.Integer(1)]
for k in range(N+2):
 fc.append(S.expand((a*fc[k]+(fc[k-1] if k else 0))/((k+2)*(k+1))))
fpoly=sum(v*x**k for k,v in enumerate(fc))
endpoint=sum(e**m*(A*fpoly+B*S.diff(fpoly,x)).subs(x,e) for m,(A,B) in enumerate(phi))
endpoint=S.series(endpoint/e,e,0,5).removeO().expand()
combined=S.series(S.exp(sum(v*e**r for r,v in h.items()))*endpoint,e,0,5).removeO().expand()
extra={'h':{str(k):str(v) for k,v in h.items()},'endpoint_over_Aiprime_epsilon':str(endpoint),'H_times_endpoint_relative':str(combined)}
Path(__file__).with_name('scalar-endpoint-checks.json').write_text(json.dumps(extra,indent=2));print(extra)
