from fractions import Fraction as F
from itertools import product
from math import ceil
import json,random
random.seed(1027)
checks=0
# Exact recurrence check over p,h0,B, including B=0.
for p,h0,B in product([2,3,5,7],[1,2,3,5],[F(0),F(1,20),F(1,2),F(1),F(7,3),F(5)]):
 a=F(1,(p-1)*p**(h0-1));c=F(p-1,p)
 assert c*a==F(1,p**h0)
 z=a;Q=c*a;previous_u=None
 for h in range(h0+1,h0+16):
  t=h+B+1;u=Q/t;d=u-c*z
  znext=z/p+u;Qnext=Q+c*znext
  unext=Qnext/(t+1);dnext=unext-c*znext
  assert dnext==t/(p*(t+1))*d
  assert unext-u==-d/(p*(t+1))
  assert d<0 and unext>u
  assert u>=c*a/(h0+B+2)
  z,Q=znext,Qnext;checks+=1
# Exact p-power-root distance valuations.
def vp_integer(n,p):
 n=abs(n);k=0
 while n and n%p==0:n//=p;k+=1
 return k

def rv(p,h):return F(1,(p-1)*p**(h-1))
def distance(p,root,target):
 k,a=root;h,b=target;L=max(k,h)
 d=b*p**(L-h)-a*p**(L-k)
 if d==0:return None
 order=L-vp_integer(d,p)
 if order==0:return F(0)
 return rv(p,order)

def prims(p,h):return [(h,b) for b in range(1,p**h) if b%p]

# Check the exact-individual-packet obstruction for all points on 8 shells.
obstruction_points=0
for h in range(1,9):
 for zeta in prims(2,h):
  v=distance(2,(h,1),zeta)
  assert v is None or v>rv(2,h)
  obstruction_points+=1
assert sum(rv(2,h) for h in range(1,9))<2

# Polynomial products with torsion roots, exact valuations including infinity.
# No numerical p-adic approximation is used.
polynomial_cases=0
max_first_success=0
for p in [2,3]:
 pool=[(0,0)]+[r for h in range(1,5) for r in prims(p,h)]
 for _ in range(400):
  h0=random.choice([1,2,3]);rho=rv(p,h0)*random.choice([F(1),F(3,2),F(2)])
  roots=random.choices(pool,k=random.randrange(0,7))
  # Also multiply by integral factors (p^m T-1), testing negative roots.
  negative_roots=[random.randrange(1,5) for _ in range(random.randrange(0,4))]
  A=sum((rho if k==0 else min(rho,rv(p,k)) for k,a in roots),F(0))
  B=A
  H=h0+ceil(p**h0*B*(h0+B+2))
  found=None
  for h in range(h0,min(H,5)+1):
   for zeta in prims(p,h):
    vals=[distance(p,r,zeta) for r in roots]
    # For p^m*T-1 the leading coefficient has valuation m and
    # its root has valuation -m, different from every target radius.
    extra_vals=[F(m)+min(rv(p,h),F(-m)) for m in negative_roots]
    assert all(v==0 for v in extra_vals)
    vals.extend(extra_vals)
    if None not in vals and sum(vals,F(0))<=A:
     found=h;break
   if found is not None:break
  # All roots are on shells at most 4; shell 5 succeeds unless g constant,
  # which succeeds on the first shell. Nonintegral-root factors are units.
  assert found is not None,(p,h0,rho,roots,A,H)
  assert found<=H
  max_first_success=max(max_first_success,found)
  polynomial_cases+=1
out={'recurrence_cases':checks,'polynomial_cases':polynomial_cases,'obstruction_points':obstruction_points,'largest_first_success_shell':max_first_success,'status':'PASS','limitations':'Exact finite sanity checks, not a Lean verification or a substitute for the mathematical proof.'}
print(json.dumps(out,indent=2))
