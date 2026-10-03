"""Independent right-support dynamic enumeration for the marginal barrier."""
from itertools import combinations
from pathlib import Path
import json
Acore=[2,0,5];L=[3,6,5,4,3,1,4];R=[2,5,5,5,1,4,7]
# Each column stores its actual left neighbors. The 10 left vertices are A then L.
cols=[]
for b in range(3):cols.append(sum(1<<i for i,t in enumerate(Acore+L)if t>>b&1))
cols+=R

def supports(J):
 states={0}
 for j in J:
  nxt=set()
  for mask in states:
   available=cols[j]&~mask
   while available:
    bit=available&-available;available-=bit;nxt.add(mask|bit)
  states=nxt
 return len(states)
forced=(0,1,2,3);remaining=tuple(range(4,10))
base=supports(forced);single={j:supports(forced+(j,))for j in remaining}
pairs={f'{j},{k}':supports(forced+(j,k))for j,k in combinations(remaining,2)}
assert base==64
common=(4,5,6,9);private=(7,8)
assert all(single[j]==74 for j in common)and all(single[j]==42 for j in private)
assert all(v==27 for v in pairs.values())
# Exhaustive rank and minimum-cover uniqueness, independently of strict-Hall argument.
max_rank=0
for mask in range(1<<10):
 J=tuple(j for j in range(10)if mask>>j&1)
 if supports(J):max_rank=max(max_rank,len(J))
assert max_rank==6
covers=[]
for chosen in combinations(range(20),6):
 left=sum(1<<i for i in chosen if i<10);right=set(i-10 for i in chosen if i>=10)
 if all(j in right or cols[j]&~left==0 for j in range(10)):covers.append(chosen)
assert covers==[(0,1,2,10,11,12)]
lin=4*74+19*2*42;quad=27*(6+8*19+19**2);disc=lin**2-4*64*quad
assert (lin,quad,disc)==(1892,14013,-7664)
out={'core_rows':Acore,'exterior_left_types':L,'exterior_right_types':R,'vertices':20,'rank':6,'unique_minimum_vertex_cover':'A union B','forced_columns':forced,'constant':base,'single_coefficients':single,'all_fifteen_pair_coefficients':27,'quadratic_specialization':[64,lin,quad],'discriminant':disc,'scope':'The right-support homogeneous marginal is not Lorentzian. This does not refute scalar ULC6.','all_checks_passed':True}
(Path(__file__).resolve().parents[1]/'data'/'marginal_barrier.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
