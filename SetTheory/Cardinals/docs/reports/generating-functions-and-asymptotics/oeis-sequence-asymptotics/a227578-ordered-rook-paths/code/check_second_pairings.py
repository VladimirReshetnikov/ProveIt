"""All-dimension d2 from the exact trace-zero saddle and Wick pairings."""
import sympy as s,json,itertools,time
k,t=s.symbols('k t'); P={0:k,1:s.Integer(0)};P.update({j:s.Symbol('P'+str(j)) for j in range(2,7)})
z=s.symbols('z');q=1/(k+1)
ell=[];f=z/(1-z)
for j in range(7):
 ell.append(s.factor(f.subs(z,q)));f=z*s.diff(f,z)
mu=ell[1];v=ell[2]/mu
# polynomial operations small fixed t truncation
N=6
def trunc(e,n=N):return s.Poly(s.expand(e),t).as_dict() if False else s.Add(*(c*t**j[0] for j,c in s.Poly(s.expand(e),t).terms() if j[0]<=n))
def power_sum_sigma(sig,m,n=N):
 powers=[s.Integer(1)]
 for h in range(1,m+1):powers.append(trunc(powers[-1]*sig,n))
 return trunc(sum(s.binomial(m,j)*powers[m-j]*(s.I*t)**j*P[j] for j in range(m+1)),n)
sig=0;sigmas={}
for r in range(2,7):
 coeff=s.expand(sum(ell[m]/s.factorial(m)*power_sum_sigma(sig,m,r) for m in range(1,r+1))).coeff(t,r)
 sr=s.factor(-coeff/(k*mu));sig+=sr*t**r;sigmas[r]=sr;print('sigma',r,flush=True)
# S/kmu=1+U to t4
U=trunc(sum(ell[m+1]/s.factorial(m)*power_sum_sigma(sig,m,4) for m in range(1,5))/(k*mu),4)
logS=trunc(sum((-1)**j*U**j/s.Integer(j) for j in range(1,5)),4)
logDen=trunc((k-1)*sum(ell[m-1]/s.factorial(m)*power_sum_sigma(sig,m,4) for m in range(1,5)),4)
logV=-k*P[2]*t*t/12-(k*P[4]+3*P[2]**2)*t**4/1440
logB=trunc(logS+logDen+logV-k*sig/t**2+v*P[2]/2,4)
B={j:s.factor(logB.coeff(t,j)) for j in range(1,5)}
poly=s.Poly(s.expand(B[4]+B[1]*B[3]+B[2]**2/2+B[1]**2*B[2]/2+B[1]**4/24),*[P[j] for j in range(2,7)])
print('terms',len(poly.terms()),flush=True)
# Enumerate trace-zero Hermitian Wick moments exactly as Laurent polynomials in k.
from functools import lru_cache
@lru_cache(None)
def pairings(items):
 if not items:return ((),)
 i=items[0];out=[]
 for a in range(1,len(items)):
  j=items[a]
  for rest in pairings(items[1:a]+items[a+1:]):out.append(((i,j),)+rest)
 return tuple(out)
@lru_cache(None)
def moment(parts):
 if not parts:return s.Integer(1)
 size=sum(parts)
 if size%2:return s.Integer(0)
 gamma=[];st=0
 for n in parts:
  gamma.extend(list(range(st+1,st+n))+[st]);st+=n
 counts={}
 for pairing in pairings(tuple(range(size))):
  for mask in range(1<<len(pairing)):
   roots=list(range(size))
   def root(a):
    while roots[a]!=a:a=roots[a]
    return a
   def union(a,b):
    a=root(a);b=root(b)
    if a!=b:roots[b]=a
   neg=mask.bit_count()
   for z,(i,j) in enumerate(pairing):
    if mask>>z&1:union(i,gamma[i]);union(j,gamma[j])
    else:union(i,gamma[j]);union(j,gamma[i])
   e=len({root(j) for j in range(size)})-neg
   counts[e]=counts.get(e,0)+(-1)**neg
 ans=s.factor(sum(c*k**e for e,c in counts.items()));print('moment',parts,ans,flush=True);return ans
# radial reductions for powers P2
D=k*k-1
moments={};res=0
for powers,coef in poly.terms():
 r=powers[0];parts=tuple(j for j,pow in zip(range(3,7),powers[1:]) for _ in range(pow));degree=sum(parts)
 mo=moment(parts)*s.prod(D+degree+2*j for j in range(r))/v**(degree//2+r)
 key=str(powers);moments[key]=str(s.factor(mo));res+=coef*mo
result=s.factor(res)
print('D2=',result,flush=True)
json.dump(dict(status='Exact symbolic radial and Wick calculation',sigma={str(j):str(v) for j,v in sigmas.items()},logB={str(j):str(v) for j,v in B.items()},d2=str(result),values={str(j):str(result.subs(k,j)) for j in range(2,9)},moments=moments),open('second-correction-pairings.json','w'),indent=2)
assert result.subs(k,3)==s.Rational(1044311,84375)
