from itertools import combinations
from fractions import Fraction
from math import prod
from pathlib import Path
import random,json,time
ROOT=Path(__file__).resolve().parent
rng=random.Random(202610011010)

def es(a):
 e=[1]+[0]*len(a)
 for x in a:
  for k in range(len(a),0,-1):e[k]+=x*e[k-1]
 return e

def covers(rows,S,T):
 # Hall on head subsets, independent of the producer's edge-extension search.
 for z in range(1,1<<len(T)):
  neighborhood={i for i in S if any((z>>h)&1 and (rows[i]>>j)&1 for h,j in enumerate(T))}
  if len(neighborhood)<z.bit_count():return False
 return True

def hall_gamma(rows,u,v,r):
 n=len(rows);g=[1]+[0]*r
 for k in range(1,r+1):
  for S in combinations(range(r),k):
   rem=[j for j in range(n) if j not in S]
   for T in combinations(rem,k):
    if covers(rows,S,T):g[k]+=prod(u[i] for i in S)*prod(v[j] for j in T)
 return g

def formula(core,u,v,w):
 r=len(core);e=es(u);E=es(w)+[0]*r;p=e[r];q=e[r-1];ee=e[r-2]
 d=c=b=0
 for j in range(r):
  incoming=[i for i in range(r) if core[i]>>j&1]
  if incoming:d+=v[j]*prod(u[i] for i in range(r)if i!=j)
  for S in combinations([i for i in range(r)if i!=j],r-2):
   if any(i in incoming for i in S):c+=v[j]*prod(u[i] for i in S)
 for j,k in combinations(range(r),2):
  rem=[i for i in range(r)if i not in (j,k)]
  if any(i!=l and core[i]>>j&1 and core[l]>>k&1 for i in rem for l in rem):
   b+=v[j]*v[k]*prod(u[i]for i in rem)
 top=[ee*E[r-2]+c*E[r-3]+b*E[r-4],q*E[r-1]+d*E[r-2],p*E[r]]
 K=Fraction(2*r,r-1)
 terms=[(q*q-K*p*ee)*E[r-1]**2,K*p*ee*(E[r-1]**2-E[r-2]*E[r]),2*(q*d-p*c)*E[r-1]*E[r-2],p*c*(2*E[r-1]*E[r-2]-K*E[r-3]*E[r]),(d*d-2*p*b)*E[r-2]**2,p*b*(2*E[r-2]**2-K*E[r-4]*E[r])]
 assert all(t>=0 for t in terms),(core,u,v,w,terms)
 assert sum(terms)==top[1]**2-K*top[0]*top[2]
 m=sum(x>0 for x in w)
 if m>=r:
  Ksharp=Fraction(2*r*r*(m-r+2),(r-1)**2*(m-r+1))
  sharpterms=[q*q*E[r-1]**2-Ksharp*p*ee*E[r-2]*E[r],2*q*d*E[r-1]*E[r-2]-Ksharp*p*c*E[r-3]*E[r],d*d*E[r-2]**2-Ksharp*p*b*E[r-4]*E[r]]
  assert all(t>=0 for t in sharpterms),(r,m,sharpterms)
  assert sum(sharpterms)==top[1]**2-Ksharp*top[0]*top[2]
 return top,terms

def test(core,u,v,w):
 r=len(core);m=len(w);rows=[x|sum(1<<j for j in range(r,r+m))for x in core]+[0]*m
 top,terms=formula(core,u,v,w)
 g=hall_gamma(rows,u+[0]*m,v+w,r)
 assert g[-3:]==top,(core,u,v,w,g,top)
 return g

start=time.time();tests=0
edges=[(i,j)for i in range(4)for j in range(4)if i!=j]
for code in range(1<<12):
 rows=[sum(1<<j for h,(i0,j)in enumerate(edges)if i0==i and code>>h&1)for i in range(4)]
 for spec in range(2):
  u=[rng.randint(1,5)for _ in range(4)];v=[rng.randint(0,5)for _ in range(4)];w=[rng.randint(1,5)for _ in range(4)]
  test(rows,u,v,w);tests+=1
for r in [4,5,6]:
 for it in range(40):
  core=[sum(1<<j for j in range(r)if i!=j and rng.random()<.4)for i in range(r)]
  m=rng.choice([0,1,2,r-1,r,r+1]);u=[rng.randint(0,5)for _ in range(r)];v=[rng.randint(0,5)for _ in range(r)];w=[rng.randint(0,5)for _ in range(m)]
  test(core,u,v,w);tests+=1
# General-r formula and six-term identity tests, independent of a vertex-count bound.
for r in range(4,21):
 for it in range(20):
  core=[sum(1<<j for j in range(r)if i!=j and rng.random()<.3)for i in range(r)]
  u=[rng.randint(0,5)for _ in range(r)];v=[rng.randint(0,5)for _ in range(r)];w=[rng.randint(0,5)for _ in range(r+3)]
  formula(core,u,v,w)
for r in range(4,13):
 for m in [r,r+1,2*r]:
  top,_=formula([0]*r,[3]*r,[2]*r,[5]*m)
  assert top[1]**2==Fraction(2*r*r*(m-r+2),(r-1)**2*(m-r+1))*top[0]*top[2]
receipt={'sharp_constant_equality_checks':27,'status' :'PASS','four_core_relations_exhausted':4096,'full_Hall_support_checks':tests,'general_formula_checks':340,'exact_arithmetic':True,'seed':202610011010,'seconds':round(time.time()-start,3)}
(ROOT/'universal_sink_verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
