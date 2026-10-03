"""Independent literal endpoint-pair enumeration; imports no grouped producer."""
from itertools import combinations
from math import prod
import json
from pathlib import Path
n=11
u=[1,1,100,100,100]+[0]*6
v=[0,240,0,0,0]+[1]*6
edges={(0,1)}|{(i,j)for i in range(5)for j in range(5,11)}
def match(S,T):
 if not T:return True
 t=T[0]
 return any((s,t)in edges and match(tuple(x for x in S if x!=s),T[1:])for s in S)
g=[1]+[0]*5;positive_pairs=0;tested=0
for k in range(1,6):
 for S in combinations(range(n),k):
  us=prod(u[s]for s in S)
  if not us:continue
  complement=[j for j in range(n)if j not in S]
  for T in combinations(complement,k):
   wt=us*prod(v[t]for t in T)
   if not wt:continue
   tested+=1
   if match(S,T):g[k]+=wt;positive_pairs+=1
assert g==[1,2052,891015,129206000,4830450000,6000000]
gap=g[2]**2-3*g[1]*g[3]
assert gap==-1484405775
assert g[5]>0
# Off-diagonal arcs define a transitive relation after adjoining the diagonal.
R=edges|{(i,i)for i in range(n)}
assert all((a,c)in R for a,b in R for bb,c in R if b==bb)
receipt={'status':'PASS','purpose':'Disproves proposed stronger constant 3, not rank-five ULC','vertices':n,'preorder':True,'actual_degree':5,'u':u,'v':v,'core_arcs':[[0,1]],'universal_sink_vertices':list(range(5,11)),'gamma':g,'gamma2_squared_minus_3gamma1gamma3':gap,'positive_weight_endpoint_pairs_tested':tested,'feasible_positive_weight_endpoint_pairs':positive_pairs}
p=Path(__file__).with_name('strengthening-counterexample-receipt.json');p.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
