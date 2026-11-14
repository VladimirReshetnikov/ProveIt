#!/usr/bin/env python3
"""Bounded exact-window search for alternative scanner51/0 helpers.

At entry, positions-1,0,1 hold1,0,1. Other cells of the radius4
window are universally quantified. Require the original two-step endpoint:
q1, head0, next1 erased, every other cell unchanged. Leaving the window
or exceeding40 steps rejects a candidate, so this is not a lower bound.
"""
from pathlib import Path
import itertools,json,hashlib
P=Path(__file__).resolve().parent
source=P/'runtime193.native.tm'
data=source.read_bytes()
assert hashlib.sha256(data).hexdigest()=='50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53'
rows={(int(q),int(b)):(int(w),1 if d=='R'else-1,int(n))for q,b,w,d,n in map(str.split,data.decode().splitlines())}
K=4;bound=40;fixed={-1:1,0:0,1:1}
free=[i for i in range(-K,K+1)if i not in fixed]

def check(act):
 worst=0
 for bits in itertools.product([0,1],repeat=len(free)):
  one={i for i,b in fixed.items()if b}|{i for i,b in zip(free,bits)if b}
  want=one-{1};q,h=51,0;seen=set()
  for k in range(bound):
   if k and q==1 and h==0 and one==want:worst=max(worst,k);break
   if abs(h)>K or(q,0)not in rows:return None
   key=(q,h,tuple(sorted(one)))
   if key in seen:return None
   seen.add(key);b=int(h in one)
   w,d,n=act if(q,b)==(51,0)else rows[q,b]
   (one.add if w else one.discard)(h);q,h=n,h+d
  else:return None
 return worst

good=[]
for q in sorted({q for q,b in rows}):
 for w,d in itertools.product([0,1],[-1,1]):
  act=(w,d,q);z=check(act)
  if z is not None:good.append([act,z])
out={'radius':K,'max_steps':bound,'fixed':fixed,'actions':good}
(P/'marker_helpers.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
