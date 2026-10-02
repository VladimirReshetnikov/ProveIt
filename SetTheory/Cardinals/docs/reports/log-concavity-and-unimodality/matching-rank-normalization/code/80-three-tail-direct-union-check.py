#!/usr/bin/env python3
if not __debug__:raise SystemExit('Run without -O; assertions are required')
from itertools import combinations
from fractions import Fraction as F
from collections import defaultdict,Counter
from pathlib import Path
import argparse,json,time
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=pa.parse_args();start=time.monotonic()
def masks(n,k):return []if k<0 or k>n else [sum(1<<i for i in I)for I in combinations(range(n),k)]
def clean(p):return {k:v for k,v in p.items()if v}
models=[]
for q,n in [(0,2),(1,2),(2,2),(1,4),(2,5),(3,5)]:models.append((f'U{q}_{n}',n,q,set(masks(n,q))))
models.append(('partition_rank2_with_loop',5,2,{(1<<i)|(1<<j)for i in (0,1)for j in (2,3)}))
from functools import reduce
models.append(('Fano',7,3,{b for b in masks(7,3)if reduce(int.__xor__,[i+1 for i in range(7)if b>>i&1])!=0}))
pairs=[3,12,48,192];bad={pairs[i]|pairs[j]for i,j in combinations(range(4),2)if (i,j)!=(2,3)}
models.append(('Vamos_type',8,4,set(masks(8,4))-bad))
pops=[(0,0,[]),(2,0,[]),(0,3,[]),(0,0,[1]),(2,3,[]),(2,0,[1]),(0,3,[1]),(0,0,[1,2]),(2,3,[1]),(2,3,[0,1]),(F(1,2),F(3,2),[F(1,3),F(2,3)])]
counts=Counter();identity_checks=boundary_checks=candidates=basis_exchange=0

def target(bases,n,q,aa,bb,L0,L1,ws):
 old=[i for i in range(n)if i not in (aa,bb)];H=sum(ws);S=sum(x*y for x,y in combinations(ws,2));mu=L0*L1+H*(L0+L1)+S;p=defaultdict(F)
 for I in range(1<<len(old)):
  actual=sum(1<<old[i]for i in range(len(old))if I>>i&1);u0=actual in bases;ua=(actual|1<<aa)in bases and not actual>>aa&1;ub=(actual|1<<bb)in bases and not actual>>bb&1;v=(actual|1<<aa|1<<bb)in bases
  # Cardinality matters: adding marked elements cannot repair an overlarge old set.
  u0=u0 and actual.bit_count()==q;ua=ua and actual.bit_count()==q-1;ub=ub and actual.bit_count()==q-1;v=v and actual.bit_count()==q-2
  for condition,a,b,z,w in [(u0,0,0,2,1),(u0,1,0,1,L0+H),(u0,0,1,1,L1+H),(u0,1,1,0,mu),(ua,1,0,2,1),(ub,0,1,2,1),(ua,1,1,1,L1),(ub,1,1,1,L0),(ua or ub,1,1,1,H),(v,1,1,2,1)]:
   if condition:p[(I,a,b,z)]+=w
 return clean(p)

def union_specialization(bases,n,q,aa,bb,L0,L1,ws):
 global candidates
 H=sum(ws);mu=L0*L1+H*(L0+L1)+sum(x*y for x,y in combinations(ws,2));assert mu>0
 plane=[F(L1)/mu,F(L0)/mu]+[F(w)/mu for w in ws];N=n+len(plane);rows=[0]*n+[1,2]+[3]*len(ws);rows[aa]=1;rows[bb]=2;old=[i for i in range(n)if i not in (aa,bb)];p=defaultdict(F)
 for C in combinations(range(N),q+2):
  candidates+=1;Cset=set(C)
  ok=False
  for x,y in combinations(C,2):
   if not ((rows[x]&1 and rows[y]&2)or(rows[x]&2 and rows[y]&1)):continue
   rest=Cset-{x,y}
   if all(i<n for i in rest)and sum(1<<i for i in rest)in bases:ok=True;break
  if not ok:continue
  plane_chosen=[i-n for i in C if i>=n];assert len(plane_chosen)<=2
  val=F(mu)
  for i in plane_chosen:val*=plane[i]
  I=sum(1<<i for i,j in enumerate(old)if j in Cset);p[(I,int(aa in Cset),int(bb in Cset),len(plane_chosen))]+=val
 return clean(p)

for label,n,q,bases in models:
 for B in bases:
  for C in bases:
   for i in range(n):
    if B>>i&1 and not C>>i&1:
     assert any(((B^(1<<i)^(1<<j))in bases)and((C^(1<<j)^(1<<i))in bases)for j in range(n)if C>>j&1 and not B>>j&1);basis_exchange+=1
 for aa,bb in combinations(range(n),2):
  counts['distinguished_pairs']+=1
  oldmask=((1<<n)-1)^(1<<aa)^(1<<bb)
  if not any(B&~oldmask==0 for B in bases):counts['nonspanning_old_pairs']+=1
  for L0,L1,ws in pops:
   H=sum(ws);mu=L0*L1+H*(L0+L1)+sum(x*y for x,y in combinations(ws,2));expected=target(bases,n,q,aa,bb,L0,L1,ws)
   if mu>0:
    assert union_specialization(bases,n,q,aa,bb,L0,L1,ws)==expected;identity_checks+=1
   else:
    # The explicit target is polynomial of degree at most two in an added
    # private activity epsilon. Exact interpolation recovers its zero limit.
    recovered=defaultdict(F)
    for eps,c in [(1,3),(2,-3),(3,1)]:
     value=union_specialization(bases,n,q,aa,bb,L0+eps,L1+eps,ws)
     assert value==target(bases,n,q,aa,bb,L0+eps,L1+eps,ws);identity_checks+=1
     for k,v in value.items():recovered[k]+=c*v
    assert clean(recovered)==expected;boundary_checks+=1
rec={'status':'PASS','abstract_matroid_models':len(models),'symmetric_basis_exchange_checks':basis_exchange,**counts,'direct_union_basis_specialization_identities':identity_checks,'zero_mu_boundary_interpolations':boundary_checks,'candidate_union_bases':candidates,'scope':'Corroboration of the ordinary direct matroid-union proof, including loops, nonspanning old sets and nonrepresentable example','seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
