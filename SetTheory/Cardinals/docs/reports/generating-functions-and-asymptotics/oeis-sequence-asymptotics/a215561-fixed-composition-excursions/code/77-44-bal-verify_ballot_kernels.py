from itertools import product
from math import factorial
from fractions import Fraction
import json
from pathlib import Path

def counts(steps,M):
 box=sorted(product(range(M+1), repeat=len(steps)),key=sum)
 walk={}
 for v in box:
  if not any(v):walk[v]=1;continue
  h=sum(i*j for i,j in zip(v,steps))
  if h<0:walk[v]=0;continue
  a=0
  for i,j in enumerate(v):
   if j:
    u=list(v);u[i]-=1;a+=walk[tuple(u)]
  walk[v]=a
 return {v:a for v,a in walk.items() if a and sum(i*j for i,j in zip(v,steps))==0}

def mul(f,g,M):
 h={}
 for a,x in f.items():
  for b,y in g.items():
   c=tuple(i+j for i,j in zip(a,b))
   if max(c)<=M:h[c]=h.get(c,0)+x*y
 return {c:z for c,z in h.items() if z}

M=3;reports=[]
for steps in [(-3,-1,1,3),(-2,-1,0,1,2)]:
 d=len(steps);E=counts(steps,M);zero=(0,)*d
 bridge={v:factorial(sum(v))//__import__('functools').reduce(lambda a,k:a*factorial(k),v,1) for v in E if v!=zero}
 q=mul(E,bridge,M)
 bad=[v for v in set(q)|set(E) if q.get(v,0)!=sum(v)*E.get(v,0)]
 report={'steps':steps,'box_max_count':M,'number_nonzero_excursion_coefficients':len(E),'bridge_exponential_identity_failed_coefficients':len(bad),'diagonal':[E[(n,)*d] for n in range(M+1)]}
 if d==5:
  powers=[{zero:1},E]
  for k in range(2,7):powers.append(mul(powers[-1],E,M))
  # Q(E)=1+(C-1)E+(BD-AF)E²+[AD²+B²F+2AF(1-C)]E³
  # +(ABDF-A²F²)E⁴+A²F²(C-1)E⁵+A³F³E⁶.
  terms=[(1,0,zero),(1,1,(0,0,1,0,0)),(-1,1,zero),(1,2,(0,1,0,1,0)),(-1,2,(1,0,0,0,1)),(1,3,(1,0,0,2,0)),(1,3,(0,2,0,0,1)),(2,3,(1,0,0,0,1)),(-2,3,(1,0,1,0,1)),(1,4,(1,1,0,1,1)),(-1,4,(2,0,0,0,2)),(1,5,(2,0,1,0,2)),(-1,5,(2,0,0,0,2)),(1,6,(3,0,0,0,3))]
  Q={}
  for sign,k,a in terms:
   for b,val in powers[k].items():
    c=tuple(i+j for i,j in zip(a,b))
    if max(c)<=M:Q[c]=Q.get(c,0)+sign*val
  badQ={str(c):v for c,v in Q.items() if v}
  report['degree_six_algebraic_identity_failed_coefficients']=badQ
 reports.append(report)
out={'type':'exact finite coefficient verification; supports but does not replace the general kernel proof','reports':reports}
print(json.dumps(out,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
