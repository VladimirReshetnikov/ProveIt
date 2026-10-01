"""Independent Boolean basis enumeration for the full left-marginal identity."""
from itertools import combinations
from functools import lru_cache
from fractions import Fraction
from random import Random
from math import prod
from pathlib import Path
import json
@lru_cache(None)
def match(rows):
 if not rows:return True
 row=min(rows,key=int.bit_count)
 if not row:return False
 rest=list(rows);rest.remove(row)
 while row:
  bit=row&-row;row-=bit
  if match(tuple(sorted(r&~bit for r in rest))):return True
 return False

def check(q,rng):
 masks=[rng.randrange(1<<q) for _ in range(2)];L=[rng.randrange(1<<q) for _ in range(rng.randrange(5))]
 ul=[rng.randrange(1,8) for _ in L];v=[rng.randrange(1,8) for _ in range(q)];a,b=[rng.randrange(7) for _ in range(2)];rr=[rng.randrange(1,8) for _ in range(rng.randrange(4))]
 c=sum(rr);d=sum(z*w for z,w in combinations(rr,2));Q=a*b+(a+b)*c+d
 if Q==0:a=b=1;Q=a*b+(a+b)*c+d
 # Original graph with singleton classes compressed by summing activities.
 rights=v+[a,b]+rr;n=len(rights);rp=[1]*(1<<n)
 for j in range(1,1<<n):
  bit=j&-j;rp[j]=rp[j-bit]*rights[bit.bit_length()-1]
 common=sum(1<<(q+2+j) for j in range(len(rr)))
 adj=[masks[0]|1<<q|common,masks[1]|1<<(q+1)|common]+L
 actual={}
 for I in range(1<<len(adj)):
  k=I.bit_count();ws=prod(ul[i-2] for i in range(2,len(adj)) if I>>i&1)
  rows=[adj[i] for i in range(len(adj)) if I>>i&1]
  z=0
  for js in combinations(range(n),k):
   J=sum(1<<j for j in js)
   if match(tuple(sorted(r&J for r in rows))):z+=rp[J]*ws
  if z:actual[I]=z
 # Independent lifted matroid bases, with s omitted and left variables marked.
 slots=(1<<q,1<<(q+1));elements=[]
 for j,w in enumerate(v):elements.append((1<<j,Fraction(1,w),None))
 for i,(m,w) in enumerate(zip(L,ul)):elements.append((m,Fraction(w),i+2))
 for i,m in enumerate(masks):elements.append((m|slots[i],Fraction(1),i))
 elements += [(slots[0],Fraction(b,Q),None),(slots[1],Fraction(a,Q),None)]
 elements += [(slots[0]|slots[1],Fraction(w,Q),None) for w in rr]
 model={};tests=0
 for inds in combinations(range(len(elements)),q+2):
  rows=tuple(sorted(elements[i][0] for i in inds));tests+=1
  if not match(rows):continue
  weight=Fraction(Q*prod(v));I=0
  for i in inds:
   _,w,index=elements[i];weight*=w
   if index is not None:I|=1<<index
  if weight:model[I]=model.get(I,0)+weight
 assert model==actual,(q,masks,L,a,b,rr,model,actual)
 # Left variables are genuinely independent in the identity, not just diagonal.
 p=[sum(z for I,z in actual.items() if I.bit_count()==k) for k in range(q+3)]
 assert all(k*(q+2-k)*p[k]**2 >= (k+1)*(q+3-k)*p[k-1]*p[k+1] for k in range(1,q+2))
 return tests
if __name__=='__main__':
 rng=Random(305731);total=0;records=[]
 for q in range(6):
  tests=sum(check(q,rng) for _ in range(30));total+=tests;records.append({'q':q,'graphs':30,'basis_subsets':tests})
 out={'seed':305731,'graphs':180,'q_values':list(range(6)),'basis_subsets_checked':total,'full_left_marginal_identity':True,'Boolean_basis_matching_without_determinants':True,'all_ULC_checks':True,'records':records}
 (Path(__file__).resolve().parents[1]/'data'/'transversal_lift_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
