from itertools import combinations,combinations_with_replacement
from fractions import Fraction as Q
from math import comb,prod
from pathlib import Path
import json
core=[2,1,0];N=8;types=[1,2,3,4,5];counts=[1,1,7,1,1];weights=[Q(15),Q(15),Q(1),Q(15),Q(1,10)]
def hall(B,A,l,rs):
 rows=[core[i] for i in A]+[7]*l
 cols=[sum(1<<i for i,r in enumerate(rows) if r>>b&1) for b in B]
 cols += [sum(1<<j for j,i in enumerate(A) if r>>i&1) for r in rs]
 for S in range(1,1<<len(cols)):
  union=0
  for j,c in enumerate(cols):
   if S>>j&1:union|=c
  if union.bit_count()<S.bit_count():return False
 return True
p=[[Q(0) for _ in range(4)] for k in range(7)]
for b in range(4):
 for B in combinations(range(3),b):
  for r in range(4):
   k=b+r
   for ids in combinations_with_replacement(range(5),r):
    wt=prod(comb(counts[i],ids.count(i))*weights[i]**ids.count(i) for i in range(5))
    if not wt:continue
    rs=[types[i] for i in ids]
    for l in range(b+1):
     if not 0<=k-l<=3:continue
     for A in combinations(range(3),k-l):
      if hall(B,A,l,rs):p[k][b]+=wt*comb(N,l)
def mul(a,b):
 c=[Q(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
gaps=[]
for k in range(1,6):
 a=mul(p[k],p[k]);b=mul(p[k-1],p[k+1]);g=[k*(6-k)*x-(k+1)*(7-k)*y for x,y in zip(a,b)];gaps.append(g)
out={'support_coefficients_by_common_B_power':[[str(x) for x in row] for row in p],'newton_gap_coefficients':[[str(x) for x in row] for row in gaps],'coefficientwise_nonnegative':all(x>=0 for row in gaps for x in row),'each_gap_nonzero':all(any(x for x in row) for row in gaps)}
certificates={}
for k,start,scale in [(1,0,5),(2,0,25),(5,4,25)]:
 c,b,a=[int(scale*x) for x in gaps[k-1][start:start+3]]
 delta=b*b-4*a*c
 if not(a>0 and delta<0):raise RuntimeError('quadratic positivity certificate')
 certificates[str(k)]={'shift':start,'scale':scale,'quadratic':[c,b,a],'discriminant':delta}
if min(gaps[2]+gaps[3]+gaps[1][3:])<0 or not all(any(x>0 for x in row) for row in gaps):raise RuntimeError('remaining gap coefficients')
out['all_common_B_fields_strict_ULC6']=True;out['quadratic_certificates']=certificates
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
