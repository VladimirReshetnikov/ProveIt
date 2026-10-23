#!/usr/bin/env python3
"""Independent bounded controls for the seeded two-root finalizer."""
import math,json
from pathlib import Path

def sq(n):return n>=0 and math.isqrt(n)**2==n
def req(p,m):
 if not p:raise AssertionError(m)

def norm(r,C,A):return (r*r-C-C*C*A)**2-4*C**3*A
cases=0;zeros=0
for C in range(-20,21):
 if abs(C)<=1:continue
 for A in range(-12,13):
  for r in range(-100,101):
   p=norm(r,C,A)
   if p==0:
    req(sq(C) and sq(A),(r,C,A));zeros+=1
   cases+=1
# Demonstrate that the C=-1 exclusion is not decorative.
req(norm(0,-1,-1)==0 and not sq(-1),'negative unit false positive')
stackcases=0
for seed in range(-12,13):
 if seed==0:continue
 for ds in __import__('itertools').product((-4,-1,2,5),repeat=3):
  C=seed; factors=[]
  for d in ds:
   b=1+4*d*C
   req(math.gcd(abs(C),abs(b))==1,'coprimality')
   req(b%4==1 and abs(b)>1,'factor modulus/nonunit')
   factors.append(b);C*=b
  req(abs(C)>1,'strict final size')
  if sq(C):req(sq(seed) and all(sq(b) for b in factors),'square descent')
  stackcases+=1
r={'status':'PASS','norm_cases':cases,'norm_zeros':zeros,'guard_stack_cases':stackcases,'scope':'finite corroboration; universal proof separate'}
Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
