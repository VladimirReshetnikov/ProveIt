"""Fresh exact bounded check of the finalizer; independent of circuit generators."""
from pathlib import Path
from math import isqrt
import json
count=hits=complete=0
for a in range(-8,9):
 for b in range(-8,9):
  va=isqrt(abs(a))+2;vb=isqrt(abs(b))+2
  for u in [-3,-1,1,3]:
   for v in range(-3,4):
    M=abs(v)+1
    for m in [-2,-1,0,1,2]:
     for n in range(9):
      om=u*m; th=u*(n+M)+v-om*(2*M+va*vb)
      value=(th*th-om*om*(a+va*va*b))**2-4*om**4*va*va*a*b
      count+=1
      if value==0:
       hits+=1
       assert a>=0 and b>=0 and isqrt(a)**2==a and isqrt(b)**2==b and v%u==0 and m>0
    if a>=0 and b>=0 and isqrt(a)**2==a and isqrt(b)**2==b and v%u==0:
     for m in [1,2]:
      Z=2*M+va*vb+isqrt(a)+va*isqrt(b);n=m*Z-M-v//u
      om=u*m;th=u*(n+M)+v-om*(2*M+va*vb)
      assert n>=2 and (th*th-om*om*(a+va*va*b))**2==4*om**4*va*va*a*b
      complete+=1
r={'assignments':count,'vanishing_cases':hits,'constructed_completeness_witnesses':complete,'status':'pass','limitation':'Finite regression only; the separate universal proof establishes equivalence.'}
Path(__file__).with_name('NINE_FINALIZER_INDEPENDENT_CHECKS.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
