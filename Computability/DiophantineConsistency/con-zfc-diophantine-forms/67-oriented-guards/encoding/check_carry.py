#!/usr/bin/env python3
"""Finite sanity checks of the separately proved borrow and mask identities."""
import itertools,json
count=0
for v in range(4,11):
 B=1<<v
 for h in range(-B//8+1,B//8):
  for incoming in (-1,0):
   a=2*h+1+incoming
   digit=a%B; outgoing=a//B
   if outgoing not in (-1,0) or ((digit&(B-2))==0)!=(h==0):
    raise ValueError('target borrow lemma')
   count+=1
masktests=0
for k in range(4):
 b=1<<k;B=1<<(k+2);w=[1,3,4];W=4;ell=sum(B**i for i in w)
 mask=B**(W+1)-1-(b-1)*ell
 if mask.bit_count()!=(W+1)*(k+2)-len(w)*k:raise ValueError('mask count')
 for zs in itertools.product(range(b),repeat=3):
  g=sum(z*B**i for z,i in zip(zs,w))
  if g&mask:raise ValueError('mask witness')
  masktests+=1
for s in range(100):
 for t in range(100):
  L=256
  R=(s+t)*L+L-1-s
  defect=s.bit_count()+t.bit_count()-(s+t).bit_count()
  if R.bit_count()!=8+t.bit_count()-defect or (defect==0)!=((s&t)==0):
   raise ValueError('carry-population identity')
print(json.dumps({'status':'PASS','target_borrow_cases':count,'mask_witness_cases':masktests,'population_cases':10000,'scope':'Finite sanity checks only; general proofs in PROOF.md'},indent=2))
