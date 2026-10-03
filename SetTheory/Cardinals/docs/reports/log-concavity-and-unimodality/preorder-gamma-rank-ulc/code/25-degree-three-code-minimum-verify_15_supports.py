"""Direct source/target subset enumeration, independent of population formula."""
from itertools import combinations
import json
from pathlib import Path
P=Path(__file__).parent
n=15
# Three four-element sink populations, with the three pair neighborhoods.
arcs={(i,j)for core,sinks in [((0,1),range(3,7)),((0,2),range(7,11)),((1,2),range(11,15))]for i in core for j in sinks}
rows=[sum(1<<j for a,j in arcs if a==i)for i in range(n)]
assert all(i!=j for i,j in arcs)
assert all((i,k)in arcs for i,j in arcs for b,k in arcs if j==b and i!=k)
assert all(i<3 for i,j in arcs) # a three-vertex cover: no matching of size4

def matching(A,B):
 if not A:return True
 i=A[0]
 return any((rows[i]>>j&1)and matching(A[1:],B[:k]+B[k+1:])for k,j in enumerate(B))
gamma=[1];tested=[]
for k in range(1,4):
 count=checks=0
 for A in combinations(range(n),k):
  others=[j for j in range(n)if j not in A]
  for B in combinations(others,k):
   checks+=1;count+=matching(A,B)
 gamma.append(count);tested.append(checks)
a,b,c=gamma[1:];D=a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c
assert gamma==[1,24,162,208] and D==-2592
report=dict(n=n,arcs=sorted(arcs),gamma=gamma,discriminant=D,support_pairs_tested=tested,matching_number=3)
(P/'direct_support_verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
