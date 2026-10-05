"""Exact checks of the excursion kernel polynomial, diagonal and zero-step removal."""
from itertools import product
from math import comb
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
cap=3;deltas=(-2,-1,0,1,2);zero=(0,)*5
D={zero:1};E={zero:1}
for c in sorted(product(range(cap+1),repeat=5),key=lambda v:(sum(v),v)):
 if c==zero:continue
 height=sum(a*b for a,b in zip(c,deltas))
 if height<0:continue
 total=0
 for i in range(5):
  if c[i]:
   old=list(c);old[i]-=1;total+=D.get(tuple(old),0)
 D[c]=total
 if height==0 and total:E[c]=total

def mul(a,b):
 out={}
 for e,v in a.items():
  for f,w in b.items():
   g=tuple(x+y for x,y in zip(e,f))
   if max(g)<=cap:out[g]=out.get(g,0)+v*w
 return {e:c for e,c in out.items() if c}
powers=[{zero:1},E]
for j in range(2,7):powers.append(mul(powers[-1],E))
# Each entry is coefficient, E exponent, x1,...,x5 exponents.
terms=[(-1,6,(3,0,0,0,3)),(-1,5,(2,0,1,0,2)),(1,5,(2,0,0,0,2)),(1,4,(2,0,0,0,2)),(-1,4,(1,1,0,1,1)),(2,3,(1,0,1,0,1)),(-1,3,(1,0,0,2,0)),(-2,3,(1,0,0,0,1)),(-1,3,(0,2,0,0,1)),(1,2,(1,0,0,0,1)),(-1,2,(0,1,0,1,0)),(-1,1,(0,0,1,0,0)),(1,1,zero),(-1,0,zero)]
res={}
for coeff,j,ex in terms:
 for e,v in powers[j].items():
  g=tuple(a+b for a,b in zip(e,ex))
  if max(g)<=cap:res[g]=res.get(g,0)+coeff*v
if any(res.values()):raise RuntimeError(('kernel identity',[(e,v) for e,v in res.items() if v][:5]))
expected=[1,35,18720,19369350];actual=[D.get((n,)*5,0) for n in range(cap+1)]
if actual!=expected:raise RuntimeError(('OEIS diagonal',actual))
for n in range(cap+1):
 B=E.get((n,n,0,n,n),0)
 if actual[n]!=comb(5*n,n)*B:raise RuntimeError(('zero-step removal',n,B))
out={'all_pass':True,'coordinate_cap':cap,'coefficient_box_size':(cap+1)**5,'nonzero_excursion_coefficients':len(E),'diagonal':actual,'basketball_diagonal':[E.get((n,n,0,n,n),0) for n in range(cap+1)]}
(ROOT/'kernel_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
