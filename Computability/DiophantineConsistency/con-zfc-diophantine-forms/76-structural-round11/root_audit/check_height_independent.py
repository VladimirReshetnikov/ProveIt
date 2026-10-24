"""Independent finite audit of the height lemma, not a proof of calibration."""
import itertools,json
from pathlib import Path

def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 while len(c)>1 and c[-1]==0:c.pop()
 return c

def ev(a,x):
 r=0
 for c in a[::-1]:r=r*x+c
 return r
count=0
rules=list(itertools.product(range(3),repeat=3))
for n in range(4):
 for rs in itertools.product(rules,repeat=n):
  a=[1];b=[1,1];R=2
  for p,q,c in rs:
   a=mul(a,[1,c]);b=mul(mul(b,[1,p]),[1,q]);R*=((1+p)*(1+q)+c)
  if sum(a)>R or sum(b)>R:raise RuntimeError('height')
  if (ev(a,R+1)==ev(b,R+1))!=(a==b):raise RuntimeError('numeric/poly equivalence')
  balance={j:sum(c==j for p,q,c in rs)-sum((p==j)+(q==j) for p,q,c in rs) for j in [1,2]}
  if (a==b)!=(balance=={1:1,2:0}):raise RuntimeError('multiplicities')
  count+=1
if ev([1,3],1)!=ev([1,2,1],1):raise RuntimeError('negative control setup')
if [1,3]==[1,2,1]:raise RuntimeError('negative control')
print(json.dumps({'status':'PASS','exhaustive_height_multiplicity_cases':count,'out_of_bound_collision_detected':True}))
