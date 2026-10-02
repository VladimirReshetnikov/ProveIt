# Independent symbolic expansion and subset matching checks.
import sympy as s, json, ast, hashlib, random
from pathlib import Path
from functools import lru_cache
import os
ROOT=Path(__file__).resolve().parent
OUT=Path(os.environ.get("OUTPUT_DIR", ROOT.parent/"results")).resolve()
OUT.mkdir(parents=True, exist_ok=True)
u,t,w,r=s.symbols('u t w r'); a=s.symbols('a1:5'); J=6
# Independent direct formal logarithm, then truncated polynomial multiplication of exponential series.
E=s.series((s.log(1+t*u)-t*u+(t*u)**2/2)/t**2-sum(a[j-1]*t**(2*j-2)*(1+t*u)**(-2*j) for j in range(1,5))+a[0],t,0,J+1).removeO().expand()
p=[s.expand(E).coeff(t,i) for i in range(J+1)]
b=[s.Integer(1)]+[s.Integer(0)]*J
for h in range(1,J+1):
 old=b[:]
 for k in range(J+1):
  b[k]=s.expand(sum(old[k-h*m]*p[h]**m/s.factorial(m) for m in range(k//h+1)))
def ex(poly):
 # Closed formula for N(1/2,1/2) moments; no moment recurrence.
 def moment(k): return sum(s.binomial(k,2*j)*s.factorial2(2*j-1)*s.Rational(1,2)**(k-j) for j in range(k//2+1))
 return s.expand(sum(c*moment(k[0]) for k,c in s.Poly(poly,u).terms()))
D=list(map(ex,b)); published=json.loads((OUT/'coefficients.json').read_text())
assert all(s.expand(x-s.sympify(y))==0 for x,y in zip(D,published['sector']))
# Direct formal division, performed as product with finite geometric inverse.
A=[x.subs(dict.fromkeys(a,0)) for x in D]
H=[x.subs({a[j]:(-1)**(j+1)*a[j]*w**(j+1) for j in range(4)},simultaneous=True) for x in D]
def mul(x,y):return [s.expand(sum(x[k]*y[i-k] for k in range(i+1))) for i in range(J+1)]
v=[0]+[-x for x in A[1:]]; inv=[s.Integer(1)]+[0]*J; power=inv[:]
for k in range(1,J+1):
 power=mul(power,v);inv=[s.expand(x+y) for x,y in zip(inv,power)]
P=mul(H,inv)
assert all(s.expand(x-s.sympify(y))==0 for x,y in zip(P,published['pgf']))
c=r*(r+1)/2
special=s.series(s.exp(c*t*t)*sum(P[h].subs({a[0]:r-c*t*t,a[1]:2*r*r-r/2,w:-1},simultaneous=True)*t**h for h in range(4)),t,0,4).removeO().expand()
assert s.expand(special-(1+r*t-r*t*t/2-r*(8*r*r-12*r+3)*t**3/24))==0
# Extract only the producer's frontier function, not execute its symbolic/numerical tests.
source=ast.parse((ROOT/'verify.py').read_text()); counts_ast=next(n for n in source.body if isinstance(n,ast.FunctionDef) and n.name=='counts')
from collections import defaultdict
ns={'defaultdict':defaultdict};exec(compile(ast.Module(body=[counts_ast],type_ignores=[]),'<producer-counts>','exec'),ns);counts=ns['counts']
def subset_counts(n,adj):
 @lru_cache(None)
 def f(mask):
  if not mask:return (1,)
  bit=mask&-mask;i=bit.bit_length()-1;rem=mask^bit;ans=list(f(rem))+[0]
  for j in range(i+1,n):
   if (rem>>j)&1 and adj(i,j):
    q=f(rem^(1<<j))
    for k,v in enumerate(q):ans[k+1]+=v
  while len(ans)>1 and ans[-1]==0:ans.pop()
  return tuple(ans)
 out=list(f((1<<n)-1));return out+[0]*(n//2+1-len(out))
I=[1,1]
for n in range(2,501):I.append(I[-1]+(n-1)*I[-2])
checks=0; triangle=[]
for n in range(15):
 row=[]
 for rr in range(n+1):
  M=counts(n,rr);assert M==subset_counts(n,lambda i,j:0<j-i<=rr)
  avoid=sum((-1)**k*x*I[n-2*k] for k,x in enumerate(M))
  assert avoid==sum(subset_counts(n,lambda i,j:j-i>rr))
  row.append(avoid);checks+=1
 triangle.append(row)
# Exact factorial bound for all simple graphs through order5, and seeded random graphs to10.
graphcases=[]
for n in range(1,6):
 edges=[(i,j) for i in range(n) for j in range(i+1,n)]
 for mask in range(1<<len(edges)):graphcases.append((n,{e for k,e in enumerate(edges) if mask>>k&1}))
rng=random.Random(414720)
for n in range(6,11):
 for _ in range(20):graphcases.append((n,{(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<.35}))
for n,edges in graphcases:
 M=subset_counts(n,lambda i,j:(i,j) in edges); delta=max(sum(i in e for e in edges) for i in range(n))
 for k,m in enumerate(M):assert s.factorial(k)*m*I[n-2*k]*2**k<=delta**k*I[n]
 m=len(edges);W=sum(s.binomial(sum(i in e for e in edges),2) for i in range(n));M2=M[2] if len(M)>2 else 0
 assert s.Rational(m*m,2)-M2==s.Rational(m,2)+W
out={'symbolic_orders':J,'path_power_count_comparisons':checks,'factorial_bound_graph_cases':len(graphcases),'constant_r_cubic':str(special),'A239144_rows_0_to_14':triangle,'source_sha256':{'verify.py':hashlib.sha256((ROOT/'verify.py').read_bytes()).hexdigest()}}
(OUT/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='A239144_rows_0_to_14'},indent=2))
