"""Independent Hall-subset coefficient and exhaustive cover verification."""
from itertools import combinations,combinations_with_replacement
from fractions import Fraction as Q
from math import comb,prod
from pathlib import Path
import json
from support_helpers import hall,discriminant

core=[2,1,0];N=8;types=[1,2,3,4,5];counts=[1,1,7,1,1]
def coefficients(epsilon):
 weights=[Q(15),Q(15),Q(1),Q(15),epsilon];out=[]
 for k in range(4):
  value=Q(0)
  for ids in combinations_with_replacement(range(5),k):
   wt=prod(comb(counts[i],ids.count(i))*weights[i]**ids.count(i) for i in range(5))
   if not wt:continue
   right=[types[i] for i in ids];num=0
   for l in range(k,4):
    for A in combinations(range(3),3+k-l):
     if hall(core,A,l,right):num+=comb(N,l)
   value+=num*wt
  out.append(value)
 return out
base=coefficients(Q(0));one=coefficients(Q(1));inc=[b-a for a,b in zip(base,one)]
if base!=[120,5300,78036,383040] or inc!=[0,204,5992,44016]:raise RuntimeError('perturbation identity')
c=coefficients(Q(1,10));P=[5*x for x in c]
if P!=[600,26602,393176,1937208]:raise RuntimeError('exact normalization')
u3=[P[1]**2-3*P[0]*P[2],P[2]**2-3*P[1]*P[3]]
u6=[8*P[1]**2-15*P[0]*P[2],5*P[2]**2-12*P[1]*P[3]]
if u3!=[-50396,-13454672] or min(u6)<=0:raise RuntimeError('gap signs')
R=[t for t,k in zip(types,counts) for _ in range(k)]
rows=[core[a]|sum(1<<(3+j) for j,t in enumerate(R) if t>>a&1) for a in range(3)]+[7]*N
best=99;covers=[]
for I in range(1<<len(rows)):
 J=0
 for i,r in enumerate(rows):
  if not I>>i&1:J|=r
 size=I.bit_count()+J.bit_count()
 if size<best:best=size;covers=[(I,J)]
 elif size==best:covers.append((I,J))
if best!=6 or covers!=[(7,7)]:raise RuntimeError(('cover census',best,covers))
# Connectedness of the explicit bipartite graph.
seen={0};changed=True
while changed:
 changed=False
 for i,r in enumerate(rows):
  for j in range(3+len(R)):
   if r>>j&1:
    a,b=i,len(rows)+j
    if (a in seen)!=(b in seen):seen.update([a,b]);changed=True
if len(seen)!=25:raise RuntimeError('not connected')
out={'vertices':25,'edges':sum(r.bit_count() for r in rows),'matching_rank':best,'unique_minimum_cover':'A union B','connected':True,'core_rows':core,'left_common_population':N,'right_types':types,'right_populations':counts,'right_activities':['15','15','1','15','1/10'],'all_left_activities':1,'forced_B_activities':1,'base_cubic':[int(x) for x in base],'perturbation_vector':[int(x) for x in inc],'conditional_cubic':[str(x) for x in c],'positive_normalization':5,'normalized_integer_cubic':[int(x) for x in P],'ulc3_gaps':[int(x) for x in u3],'shifted_ulc6_gaps':[int(x) for x in u6],'discriminant':int(discriminant(P)),'left_cover_masks_checked':1<<len(rows),'all_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
