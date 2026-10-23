#!/usr/bin/env python3
"""Independent finite audit of the new unweighted-radical guard."""
from itertools import product
from pathlib import Path
import json,math

def require(x,m):
 if not x:raise AssertionError(m)
def sq(x):return x>=0 and math.isqrt(x)**2==x
count=0;zero_spectators=0
for seed,d1,d2,d3,a1,z1,z2,z3 in product(range(-4,5),(-4,-1,2,5),(-1,2),(-1,2),range(-4,5),(-1,1),(-1,1),(-1,1)):
 if seed==0:continue
 C0=seed;B1=1+4*d1*C0*z1*z1;C1=C0*B1;B2=1+4*d2*C1*z2*z2;C2=C1*B2;B3=1+4*d3*C2*a1*z3*z3;C=C2*B3
 require(C!=0 and C!=a1,'nonzero/noncoincident')
 require(math.gcd(abs(B3),abs(a1))==1,'spectator coprimality')
 if sq(C):
  require(sq(seed) and all(sq(v) for v in [B1,B2,B3]),'square descent')
  require(d1>0 and d2>0,'first two guards')
  if a1>0:require(d3>0,'third guard with positive spectator')
 if a1==0:
  require(B3==1,'zero spectator deliberately not excluded by last factor');zero_spectators+=1
 count+=1
# A raw two-root norm has false zeros at negative coincident radicands.
require((0-(-1)-(-1))**2-4*(-1)*(-1)==0,'coincident negative control')
result={'status':'PASS','guard_cases':count,'zero_spectator_cases':zero_spectators,'coincident_negative_control':'detected','scope':'Finite checks supplement the universal argument; positivity of spectator requires source bootstrap.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
