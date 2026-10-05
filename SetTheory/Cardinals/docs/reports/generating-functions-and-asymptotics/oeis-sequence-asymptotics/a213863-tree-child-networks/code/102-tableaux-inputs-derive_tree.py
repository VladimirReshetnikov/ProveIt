import sympy as S
import json,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
x,k,t=S.symbols('x k t')
c=S.Rational(2,3)
v=c*x+k
M=int(sys.argv[1]) if len(sys.argv)>1 else 7

def add(a,b):return [S.expand(i+j) for i,j in zip(a,b)]
def scale(a,c):return [S.expand(c*i) for i in a]
def D(a):
 p,q=a
 return [S.expand(S.diff(p,x)+v*q),S.expand(p+S.diff(q,x))]
def L(a):return add(D(D(a)),scale(a,-v))
def mul(a,b,n=M):
 out=[S.S(0)]*(n+1)
 for i,ai in enumerate(a[:n+1]):
  if ai==0:continue
  for j,bj in enumerate(b[:n+1-i]):
   if bj!=0:out[i+j]+=ai*bj
 return [S.expand(y) for y in out]
def powser(a,j,n=M):
 out=[S.S(1)]+[S.S(0)]*n
 for z in range(j):out=mul(out,a,n)
 return out
def ratseries(expr,n=M):
 expr=S.series(expr,t,0,n+1).removeO().expand()
 return [expr.coeff(t,i) for i in range(n+1)]
def sumseries(a,b):return [S.expand(i+j) for i,j in zip(a,b)]
def shift(fp,j,q,eps,n):
 # t'^j f_j((x+eps*t)(1-q*t^3)^(-1/3))
 fac=[S.S(0)]*(n+1)
 for i in range((n-j)//3+1):fac[j+3*i]=S.rf(S.Rational(j,3),i)/S.factorial(i)*q**i
 stretch=[S.S(0)]*(n+1)
 for i in range(n//3+1):stretch[3*i]=S.rf(S.Rational(1,3),i)/S.factorial(i)*q**i
 delta=[S.expand(x*stretch[z]+(eps*stretch[z-1] if z else 0)-(x if z==0 else 0)) for z in range(n+1)]
 power=[S.S(1)]+[S.S(0)]*n
 ans=[[S.S(0)]*(n+1) for _ in range(2)]
 for d in range(n-j+1):
  sm=mul(fac,power,n)
  for a in range(2):
   for z in range(n+1):ans[a][z]+=sm[z]*fp[a]/S.factorial(d)
  power=mul(power,delta,n);fp=D(fp)
 return [[S.expand(z) for z in c] for c in ans]
def fullshift(fs,q,eps,n):
 ans=[[S.S(0)]*(n+1) for _ in range(2)]
 for j,fp in enumerate(fs):
  new=shift(fp,j,q,eps,n)
  ans=[sumseries(a,b) for a,b in zip(ans,new)]
 return ans

def derive():
 fs=[[S.S(1),S.S(0)]]
 sig=[S.S(2),S.S(0),k]
 weightu=ratseries((3+x*t*t+t**3)/(3+3*x*t*t-3*t**3))
 weightv=ratseries((3+x*t*t+t**3)/(3+x*t*t-t**3))
 for n in range(3,M+1):
  minus=fullshift(fs,1,-1,n);plus=fullshift(fs,1,1,n)
  rhs=[sumseries(mul(weightu,a,n),mul(weightv,b,n)) for a,b in zip(minus,plus)]
  lhs=[[sum(sig[z-j]*fs[j][a] for j in range(len(fs)) if 0<=z-j<len(sig)) for z in range(n+1)] for a in range(2)]
  residual=[S.expand(rhs[a][n]-lhs[a][n]) for a in range(2)]
  j=n-2
  target=S.Poly(S.expand(2*residual[0]-S.diff(residual[1],x)),x)
  degree=max(0,int(target.degree())) if not target.is_zero else 0
  qc=[S.S(0)]*(degree+4)
  for dd in range(degree,-1,-1):
   qc[dd]=S.expand((-target.nth(dd)-4*k*(dd+1)*qc[dd+1]+(dd+3)*(dd+2)*(dd+1)*qc[dd+3])/(2*c*(2*dd+1)))
  qtilde=sum(qc[dd]*x**dd for dd in range(degree+1))
  sigma=-c*qc[0]
  q=S.expand(qtilde+sigma/c)
  pp=S.integrate((-residual[1]-S.diff(q,x,2))/2,x)-S.diff(q,x).subs(x,0)
  fp=[S.factor(pp),S.factor(q)]
  if any(S.expand(z)!=0 for z in add(L(fp),add(residual,[-sigma,0]))):raise AssertionError(('residual',n))
  if q.subs(x,0)!=0 or S.expand(pp+S.diff(q,x)).subs(x,0)!=0:raise AssertionError(('gauge',n))
  fs.append(fp);sig.append(S.factor(sigma))
  print('j',j,'sigma',sig[-1],'P,Q',fp,flush=True)
 return fs,sig
if __name__=='__main__':
 fs,sig=derive()
 allout={'f':[[str(z) for z in p] for p in fs],'sigma':[str(z) for z in sig]}
 with open(BASE/f'formal_{M}.json','w') as f:json.dump(allout,f,indent=2)
