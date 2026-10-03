"""Exact leading-gap and explicit-threshold checks on genuine covers."""
from itertools import combinations
from math import prod
from fractions import Fraction
from pathlib import Path
import random,json
rng=random.Random(372159)

def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out

def one(a,q):
 h=a-2;d=q+2;r=a+q;n=a+q+1;m=r+1
 # The exterior blocks contain fixed matchings and optional extra edges.
 rows=[0]*n
 for i in range(a):
  for j in range(q):
   if rng.randrange(2):rows[i]|=1<<j
  for j in range(a+1):
   if i==j or rng.randrange(2):rows[i]|=1<<(q+j)
 for i in range(q+1):
  for j in range(q):
   if i==j or rng.randrange(2):rows[a+i]|=1<<j
 cols=[sum(1<<i for i,row in enumerate(rows)if row>>j&1)for j in range(m)]
 u=[rng.randrange(1,6)for _ in range(n)];v=[rng.randrange(1,6)for _ in range(m)];F=sum(1<<(q+j)for j in range(h))
 P=[[0]*(h+1)for _ in range(r+1)];dp=[None]*(1<<m);dp[0]={0}
 for J in range(1<<m):
  k=J.bit_count()
  if J:
   bit=J&-J;idx=bit.bit_length()-1;states=set()
   for I in dp[J^bit]:
    avail=cols[idx]&~I
    while avail:
     z=avail&-avail;avail-=z;states.add(I|z)
   dp[J]=states
  if k>r:assert not dp[J];continue
  c=sum(prod(u[i]for i in range(n)if I>>i&1)for I in dp[J])*prod(v[j]for j in range(m)if J>>j&1)
  P[k][(J&F).bit_count()]+=c
 b=[P[k][k]for k in range(h+1)];c=[P[h+j][h]for j in range(d+1)]
 assert all(x>0 for x in b+c)
 gaps=[];bound=Fraction(0)
 for k in range(1,r):
  A=mul(P[k],P[k]);B=mul(P[k-1],P[k+1]);g=[k*(r-k)*x-(k+1)*(r-k+1)*y for x,y in zip(A,B)]
  while g[-1]==0:g.pop()
  assert g[-1]>0 and len(g)-1==(2*k if k<=h else 2*h)
  if k<h:assert g[-1]>=Fraction((k+1)*d,h-k)*b[k-1]*b[k+1]
  elif k==h:assert g[-1]==h*d*c[0]**2
  else:
   j=k-h;assert g[-1]>=Fraction(h*(d-j+1),j)*c[j-1]*c[j+1]
  bound=max(bound,Fraction(sum(max(-z,0)for z in g[:-1]),g[-1]));gaps.append(g)
 threshold=bound.numerator//bound.denominator+1
 assert all(sum(z*threshold**j for j,z in enumerate(g))>0 for g in gaps)
 return threshold
values=[one(a,q)for a in(3,4,5)for q in(0,1,2)for trial in range(4)]
out={'status':'passed','graphs':len(values),'left_cover_sizes':[3,4,5],'right_cover_sizes':[0,1,2],'all_fields_positive_integer':True,'leading_coefficient_formulas_checked':True,'coefficient_dominance_thresholds_verified':True,'largest_threshold_in_tests':max(values)}
(Path(__file__).resolve().parents[1]/'data'/'eventual_scaling_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
