"""Independent d2 verification by substitution and Gaussian integration-by-parts."""
import sympy as s,json,hashlib,ast
from functools import lru_cache
from pathlib import Path
root=Path(__file__).resolve().parent.parent
raw=json.loads((root/'data'/'second-correction-pairings.json').read_text())
k,t,z=s.symbols('k t z'); P={0:k,1:s.Integer(0),**{j:s.Symbol('P'+str(j)) for j in range(2,7)}}
loc={'k':k,**{str(P[j]):P[j] for j in range(2,7)}}
sig={j:s.sympify(raw['sigma'][str(j)],locals=loc) for j in range(2,7)}
# Truncated-series convolution, rather than producer's expanded-expression engine.
def add(*arr):return [sum(a[j] for a in arr) for j in range(7)]
def mul(a,b):return [s.expand(sum(a[j]*b[n-j] for j in range(n+1))) for n in range(7)]
def scale(a,c):return [c*x for x in a]
one=[s.Integer(1)]+[s.Integer(0)]*6
sigma=[0,0]+[sig[j] for j in range(2,7)]
powers=[one]
for j in range(1,7):powers.append(mul(powers[-1],sigma))
W=[]
for m in range(7):
 W.append([sum(s.binomial(m,j)*s.I**j*P[j]*powers[m-j][n-j] for j in range(min(m,n)+1)) for n in range(7)])
# Euler derivatives of h from independent rational differentiation.
f=z/(1-z); h=[]
for j in range(7):h.append(s.factor(f.subs(z,1/(k+1))));f=s.diff(f,z)*z
constraint=add(*[scale(W[m],h[m]/s.factorial(m)) for m in range(1,7)])
for r in range(1,7):assert s.simplify(s.factor(constraint[r]))==0,('implicit',r)
U=add(*[scale(W[m],h[m+1]/(s.factorial(m)*k*h[1])) for m in range(1,6)])
# Only degrees through four are used; h_6 is sufficient.
lograd=[0]*7; up=one
for j in range(1,5):
 up=mul(up,U);lograd=add(lograd,scale(up,s.Rational((-1)**j,j)))
logden=add(*[scale(W[m],(k-1)*h[m-1]/s.factorial(m)) for m in range(1,5)])
logb={}
for r in range(1,5):
 V= -k*P[2]/12 if r==2 else -(k*P[4]+3*P[2]**2)/1440 if r==4 else 0
 logb[r]=s.factor(lograd[r]+logden[r]+V-k*sig[r+2])
 assert s.factor(logb[r]-s.sympify(raw['logB'][str(r)],locals=loc))==0,('logB',r)
# Independent trace-zero Gaussian Schwinger-Dyson recursion at covariance beta=1.
# Every call reduces total matrix degree by 2. P0=k and P1=0.
@lru_cache(None)
def moment(parts):
 parts=tuple(sorted(parts))
 if 1 in parts:return s.Integer(0)
 zeros=parts.count(0)
 if zeros:return k**zeros*moment(tuple(x for x in parts if x))
 if not parts:return s.Integer(1)
 if sum(parts)%2:return s.Integer(0)
 m,*rest=parts;rest=tuple(rest)
 ans=sum(moment(tuple(sorted((j,m-2-j)+rest))) for j in range(m-1))
 ans-=s.Rational(m-1,1)/k*moment(tuple(sorted((m-2,)+rest)))
 for i,r in enumerate(rest):
  tail=rest[:i]+rest[i+1:]
  ans+=r*(moment(tuple(sorted((m+r-2,)+tail)))-moment(tuple(sorted((m-1,r-1)+tail)))/k)
 return s.factor(ans)
poly=s.Poly(s.expand(logb[4]+logb[1]*logb[3]+logb[2]**2/2+logb[1]**2*logb[2]/2+logb[1]**4/24),*[P[j] for j in range(2,7)])
beta=h[2]/h[1];value=0;verified={}
for ex,coef in poly.terms():
 parts=tuple(j for j,exp in zip(range(2,7),ex) for _ in range(exp))
 mo=s.factor(moment(parts)/beta**(sum(parts)//2))
 assert s.factor(mo-s.sympify(raw['moments'][str(ex)],locals=loc))==0,('moment',ex)
 verified[str(parts)]=str(mo);value+=coef*mo
value=s.factor(value)
assert s.factor(value-s.sympify(raw['d2'],locals=loc))==0
out={'implicit_residual_through_t6':'0','logB_comparison_through_t4':'0','independent_IBP_moments':verified,'d2':str(value),'status':'All independent assertions passed'}
print(json.dumps(out,indent=2))
Path('second-independent-check.json').write_text(json.dumps(out,indent=2)+'\n')
