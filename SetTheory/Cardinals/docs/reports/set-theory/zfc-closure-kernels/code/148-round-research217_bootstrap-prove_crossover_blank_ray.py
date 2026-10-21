#!/usr/bin/env python3
"""Owned exact finite prefix followed by a literal outward-ray induction."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent/'crossover30';P=D/'initialized217.native.tm'
T={}
for line in P.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,n=line.split();T[int(q),int(b)]=int(w),1 if d=='R'else -1,int(n)
assert T[35,0]==(1,1,35)
q=h=0;ones=set();trace=[]
for tick in range(86):
 if q==35 and h>max(ones,default=h-1):break
 b=int(h in ones);w,d,n=T[q,b];trace.append([tick,q,h,b,w,d,n])
 if w:ones.add(h)
 else:ones.discard(h)
 q,h=n,h+d
else:raise AssertionError('expected ray not reached')
assert(tick,q,h,sorted(ones))==(85,35,7,[-3,-2])
r=dict(status='EXACT_BLANK_OUTWARD_RAY_PROVED',table_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),prefix_steps=tick,state=q,head=h,ones=sorted(ones),ray_transition=[35,0,1,1,35],trace=trace,induction='At ray entry every cell at or right ofhead7 iszero. Afterk further steps state35 is at7+k, all cells at or right of7+k remainzero, and only cells7 through6+k have been newly written1. The literal35/0=1R35 row preserves this invariant and never halts. This is an exact unbounded nonhalting proof, not a finite cap inference.',scope='This exact unrepaired crossover217 composition is initialized-runtime correct but unconditionally nonhalting from blank. This does not rule out a repair or another217-state table.')
(D/'FOLDED217_BLANK_RAY.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k not in('trace','induction')})
