"""Exact standard-library checker for the final side-matroid Rayleigh identity."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import defaultdict,Counter
import json,hashlib
R=Path(__file__).resolve().parent
P=R/'side1565_rayleigh_0_9_certificate.json';D=json.loads(P.read_text())
assert D['simple_masks']==[1,2,4,8,16,3,7,23,15,31]
assert D['pair']==[0,9] and D['remaining_elements']==list(range(1,9))
def feasible(cols,used=0):
 if not cols:return True
 options=cols[0]&~used
 while options:
  bit=options&-options;options-=bit
  if feasible(cols[1:],used|bit):return True
 return False
bases={sum(1<<i for i in b)for b in combinations(range(10),5)if feasible([D['simple_masks'][i]for i in b])}
assert len(bases)==198 and bases==set(D['bases'])
f=[[],[],[],[]]
for b in bases:f[2*(b&1)+((b>>9)&1)].append(tuple((b>>i)&1 for i in range(1,9)))
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
q=defaultdict(int)
for a in f[1]:
 for b in f[2]:q[add(a,b)]+=1
for a in f[0]:
 for b in f[3]:q[add(a,b)]-=1
q={e:c for e,c in q.items()if c};assert len(q)==397
bs=sorted(tuple(t//2 for t in e)for e in q if all(t%2==0 for t in e));assert len(bs)==37 and bs==[tuple(e)for e in D['basis_monomials']]
count=Counter(add(a,b)for a in bs for b in bs)
G=[[F(q.get(add(a,b),0),count[add(a,b)])for b in bs]for a in bs]
assert G==[[F(x)for x in row]for row in D['gram']]
res=[row[:]for row in G];expanded=defaultdict(F)
assert len(D['terms'])==32
for t in D['terms']:
 w=F(t['weight']);v=list(map(F,t['vector']));assert w>0 and len(v)==37
 for i in range(37):
  for j in range(37):
   c=w*v[i]*v[j];res[i][j]-=c;expanded[add(bs[i],bs[j])]+=c
assert all(x==0 for row in res for x in row)
assert {e:c for e,c in expanded.items()if c}==q
# Positive Schur pivots plus a zero residual provide an independent rank check.
S=[row[:]for row in G];rank=0
while any(x for row in S for x in row):
 assert all(S[i][i]>=0 for i in range(37))
 k=next(i for i in range(37)if S[i][i]>0);w=S[k][k];v=[S[i][k]/w for i in range(37)]
 S=[[S[i][j]-w*v[i]*v[j]for j in range(37)]for i in range(37)];rank+=1
assert rank==32
print(json.dumps({'passed':True,'bases':198,'rayleigh_monomials':397,'gram_dimension':37,'gram_rank':32,'positive_rational_squares':32,'all_real_identity':True,'certificate_sha256':hashlib.sha256(P.read_bytes()).hexdigest()},indent=2))
