"""Exact checks from the full endpoint-support sum, independent of top formulas."""
from math import comb
from fractions import Fraction
from itertools import combinations
from random import Random
import json
from pathlib import Path

def C(n,k):return comb(n,k) if 0<=k<=n else 0

def coefficients(a,b,n,m,w):
 return [sum(C(a,i)*C(n,k-i)*C(b,j)*C(m,k-j)*w**j
             for i in range(a+1) for j in range(b+1) if i+j>=k)
         for k in range(a+b+1)]

def top_formula(a,b,n,m,w):
 X,Y,Z=(C(n,b-i) for i in range(3));R0,R1,R2=(C(m,a-i) for i in range(3))
 return [((C(a,2)*X+a*Y+Z)*R2*w**b+b*(a*Y+Z)*R1*w**(b-1)+C(b,2)*Z*R0*w**(b-2)),
         (a*X+Y)*R1*w**b+b*Y*R0*w**(b-1),X*R0*w**b]

def matchable(I,J,a,b):
 adj={i:[j for j in J if i<a or j<b] for i in I};owner={}
 def augment(i,seen):
  for j in adj[i]:
   if j in seen:continue
   seen.add(j)
   if j not in owner or augment(owner[j],seen):owner[j]=i;return True
  return False
 return all(augment(i,set()) for i in I)

checks=0
for a,b,n,m in [(1,1,1,2),(1,2,2,2),(2,2,2,2),(2,3,3,2),(3,2,2,3),(3,3,3,3)]:
 w=3;direct=[0]*(a+b+1)
 for k in range(a+b+1):
  for I in combinations(range(a+n),k):
   for J in combinations(range(b+m),k):
    if matchable(I,J,a,b):direct[k]+=w**sum(j<b for j in J)
 assert direct==coefficients(a,b,n,m,w);checks+=1
rng=Random(20261001)
for _ in range(100):
 a,b=rng.randrange(2,11),rng.randrange(2,15);n=b+rng.randrange(8);m=a+rng.randrange(10);w=rng.randrange(1,100)
 assert coefficients(a,b,n,m,w)[-3:]==top_formula(a,b,n,m,w);checks+=1
records=[]
for a,b,n,m,w,primitive,scalar in [
 (8,42,44,31,10000,[-1,5958,421173],Fraction(98)),
 (8,42,44,31,6028,[-1,5958,421173],Fraction(98)),
 (8,30,32,1000,3000000,[-2404,4878807600,10888224221475],Fraction(3,2272)),
 (8,30,32,1000,2031684,[-2404,4878807600,10888224221475],Fraction(3,2272))]:
 p=coefficients(a,b,n,m,w);r=a+b
 assert p[-3:]==top_formula(a,b,n,m,w)
 delta=(r-1)*p[-2]**2-2*r*p[-3]*p[-1]
 D=C(n,b)*C(m,a-1);quad=sum(primitive[i]*w**(2-i) for i in range(3))
 assert delta==scalar*D*D*w**(2*b-2)*quad<0
 margins=[k*(r-k)*p[k]**2-(k+1)*(r-k+1)*p[k-1]*p[k+1] for k in range(1,r)]
 records.append({'shape':[a,b,n,m],'rank':r,'vertices':r+n+m,'weight':w,'primitive_quadratic':primitive,'quadratic_value':quad,'positive_factor_scalar':str(scalar),'failing_indices':[k+1 for k,g in enumerate(margins) if g<0],'full_coefficients':p,'last_gap':delta})
output={'independent_boolean_shapes':6,'random_full_sum_top_formula_checks':100,'witnesses':records}
Path(__file__).with_name('full_hall_verification.json').write_text(json.dumps(output,indent=2))
print('PASS',checks,'independent/regression checks;',[(r['rank'],r['weight'],r['failing_indices']) for r in records])
