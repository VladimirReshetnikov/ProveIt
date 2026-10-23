#!/usr/bin/env python3
"""Independent exact checks of the signed-borrow sparse target padding."""
from itertools import product,combinations
from pathlib import Path
import json

def req(p,m):
    if not p: raise AssertionError(m)
local=0
for B in (8,16,32,64):
    for h in range(-B//4+1,B//4):
        for incoming in (-1,0):
            digit=(2*h+1+incoming)%B
            req(((digit&(B-2))==0)==(h==0),(B,h,incoming))
            req((2*h+1+incoming)//B in(-1,0),'target borrow bound')
            req((2*h+incoming)//B in(-1,0),'ordinary borrow bound')
            local+=1
whole=0
for B in (8,16):
    for hs in product((-1,0,1),repeat=5):
        for bits in range(1,32):
            targets=[j for j in range(5) if bits>>j&1]
            J=sum((2*h+(j in targets))*B**j for j,h in enumerate(hs))
            if J<0: continue
            mask=sum((B-2)*B**j for j in targets)
            req(((J&mask)==0)==all(hs[j]==0 for j in targets),(B,hs,targets,J))
            whole+=1
# Without the extra +1, an incoming borrow at a zero target is rejected.
req(((-1)%8)&6!=0,'unpadded zero negative control')
r={'status':'PASS','local_cases':local,'whole_integer_cases':whole,
   'unpadded_zero_negative_control':'rejected','scope':'finite corroboration of signed carry induction'}
Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
