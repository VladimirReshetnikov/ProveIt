#!/usr/bin/env python3
"""Independent standard-library Hall-kernel and exact rational identity audit.
This does not import any producer code or use optimization/SymPy.
"""
import hashlib,itertools,json,math,time
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
BASE=Path('/workspace/shared/preorder-gamma-degree4/structural-template26/pair-compatibility')
OUT=Path(__file__).parent
ZERO=(0,)*5
TYPES=(1,2,3,5,7)
def clean(p): return {e:c for e,c in p.items() if c}
def add(*ps):
 r=defaultdict(F)
 for p in ps:
  for e,c in p.items():r[e]+=c
 return clean(r)
def scale(p,c):return clean({e:v*c for e,v in p.items()})
@lru_cache(None)
def uni(a,b):
 # Count ordered subsets of fixed union, independently of factorial formula.
 r=[]
 for t in range(max(a,b),a+b+1):
  full=(1<<t)-1; aa=[sum(1<<i for i in z) for z in itertools.combinations(range(t),a)]
  bb=[sum(1<<i for i in z) for z in itertools.combinations(range(t),b)]
  n=sum(x|y==full for x in aa for y in bb)
  if n:r.append((t,n))
 return tuple(r)
def mul(p,q):
 r=defaultdict(F)
 for a,x in p.items():
  for b,y in q.items():
   for zz in itertools.product(*(uni(i,j) for i,j in zip(a,b))):
    r[tuple(z[0] for z in zz)]+=x*y*math.prod(z[1] for z in zz)
 return clean(r)
def constant(c):return {} if not c else {ZERO:F(c)}
def var(i):e=list(ZERO);e[i]=1;return {tuple(e):F(1)}
def choose(p,k):
 r=constant(1)
 for i in range(k):r=mul(r,add(p,constant(-i)))
 return scale(r,F(1,math.factorial(k)))
def increment(p,i):
 r=defaultdict(F)
 for e,c in p.items():
  r[e]+=c
  if e[i]:ee=list(e);ee[i]-=1;r[tuple(ee)]+=c
 return clean(r)
def quotas(total,n=5):
 if n==1:yield (total,);return
 for i in range(total+1):
  for rest in quotas(total-i,n-1):yield (i,)+rest

def mandatory_counts(q):
 ext=[t for t,n in zip(TYPES,q) for _ in range(n)];h=len(ext);n=3+h
 adj=[0,0,1]+ext
 assert all(a>=0 and a<8 for a in adj)
 def admits(tails,heads):
  poss={0}
  for v in tails:
   nxt=set()
   for used in poss:
    for w in heads:
     if (adj[v]>>w)&1 and not (used>>w)&1:nxt.add(used|(1<<w))
   poss=nxt
  return bool(poss)
 counts=[]
 for k in range(4):
  count=0
  if h<=k:
   for ct in itertools.combinations(range(3),k-h):
    for heads in itertools.combinations([v for v in range(3) if v not in ct],k):
     if admits(tuple(ct)+tuple(range(3,n)),heads):count+=1
  counts.append(count)
 return counts

def ex_check(e):
 assert isinstance(e,list) and len(e)==5 and all(type(v)is int and v>=0 for v in e)
 return tuple(e)
def read_poly(terms):
 r=defaultdict(F)
 for e,c in terms:r[ex_check(e)]+=F(c)
 return clean(r)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
start=time.perf_counter();Q=[{} for _ in range(4)];num=0
for total in range(4):
 for q in quotas(total):
  num+=1
  for k,c in enumerate(mandatory_counts(q)):
   if c:Q[k][q]=F(c)
# Quota degree>3 is impossible because every exterior must occupy a distinct
# tail and be matched to one of three core heads. This is an exact kernel.
a,b,c,d,e=[var(i) for i in range(5)]
A=add(constant(1),a,b,scale(c,2),scale(d,2),scale(e,3))
B=add(mul(a,b),mul(a,c),mul(a,d),scale(mul(a,e),2),mul(b,c),scale(mul(b,d),2),scale(mul(b,e),2),scale(mul(c,d),3),scale(mul(c,e),3),scale(mul(d,e),3),choose(c,2),choose(d,2),scale(choose(e,2),3),b,c,e)
T=add(mul(b,add(mul(add(d,e),add(a,c)),choose(add(d,e),2))),mul(a,add(mul(c,d),mul(c,e),mul(d,e),choose(e,2))),choose(add(c,d,e),3),scale(choose(c,3),-1),scale(choose(d,3),-1))
assert Q==[constant(1),A,B,T], 'Claimed Q formulas differ from mandatory Hall counts'
cert_path=BASE/'distinct_deletion_cross_certificates.json';data=json.loads(cert_path.read_text())
assert data['variables']==list('abcde')
recs=data['certificates'];assert len(recs)==10
assert {tuple(r['deletions']) for r in recs}==set(itertools.combinations(range(5),2))
results=[]
for rec in recs:
 i,j=rec['deletions'];assert i<j
 assert rec['population_shift']==[int(k in (i,j)) for k in range(5)]
 # At m=x+ei+ej, deleting i leaves x+ej and deleting j leaves x+ei.
 qi=[increment(z,j) for z in Q];qj=[increment(z,i) for z in Q]
 target=add(scale(mul(qi[2],qj[2]),2),scale(mul(qi[1],qj[3]),-3),scale(mul(qj[1],qi[3]),-3))
 rhs={}
 for sq in rec['squares']:
  w=F(sq['weight']);assert w>0
  m=ex_check(sq['multiplier']);form=read_poly(sq['form']);assert form
  rhs=add(rhs,scale(mul({m:F(1)},mul(form,form)),w))
 for ex,co in rec['positive_binomial_remainder']:
  ex=ex_check(ex);co=F(co);assert co>0
  rhs=add(rhs,{ex:co})
 assert rhs==target, (i,j,add(rhs,scale(target,-1)))
 row={'deletions':[i,j],'squares':len(rec['squares']),'positive_remainder_terms':len(rec['positive_binomial_remainder']),'target_terms':len(target),'status':'PASS'}
 results.append(row);print(row,flush=True)
# Exact dependency pin: actual-degree <=3 vertex-weighted theorem.
dep=Path('/workspace/shared/weighted-vertex-seven-independent-audit/approval_receipt.json')
source=Path('/workspace/shared/weighted-preorder-gamma/VERTEX_WEIGHTED_DEGREE3_THEOREM.md')
dr=json.loads(dep.read_text());assert dr['verdict']=='approved';assert sha(source)==dr['source_theorem_sha256']
receipt={'verdict':'PASS','scope':'Exact Q Hall kernel, ten distinct-deletion cross identities, and pinned vertex-weighted degree-three dependency. Convex-hull and specialization mathematics reviewed separately. This file alone does not certify a full template26 replacement proof.','date_utc':'2026-10-01','kernel_quotas':num,'kernel_coefficients':sum(map(len,Q)),'distinct_pairs':10,'square_terms':sum(z['squares'] for z in results),'positive_remainder_terms':sum(z['positive_remainder_terms'] for z in results),'pairs':results,'sha256':{str(p):sha(p) for p in [cert_path,BASE/'DELETION_MIXTURE_LEMMA.md',dep,source,Path(__file__)]},'seconds':time.perf_counter()-start}
(OUT/'deletion_mixture_algebra_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('pairs','sha256')},indent=2))
