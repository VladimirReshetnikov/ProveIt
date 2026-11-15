#!/usr/bin/env python3
"""Narrow marker-restoring fold search (not a state-count lower bound).

Run from the unpacked archive with:
  python3 -B research/marker_fold_search.py
The input and output can be changed with --machine and --output.
"""
from pathlib import Path
from itertools import product
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--machine',type=Path,default=ROOT/'machines/PA194LCG/machine.native.tm')
parser.add_argument('--output',type=Path)
parser.add_argument('--radius',type=int,default=4)
parser.add_argument('--max-steps',type=int,default=18)
args=parser.parse_args()
assert args.radius>=2 and args.max_steps>=1
base=args.machine
out=args.output or Path(__file__).with_suffix('.json')

R={}
for l in base.read_text().splitlines():
 z=l.split()
 if len(z)==5:R[int(z[0]),int(z[1])]=(int(z[2]),z[3]=='R',int(z[4]))
q=83; banned={83,190};radius=args.radius;limit=args.max_steps
controls=sorted({a for a,b in R}-{190,83})
results={}
for b in (0,1):
 tests=[]
 for marker in (0,1):
  positions=[i for i in range(-radius,radius+1) if i not in(-1,0)]
  for bits in product((0,1),repeat=len(positions)):
   tape={-1:marker,0:b,**dict(zip(positions,bits))}
   want=dict(tape);want[-1]=1
   if b:want[0]=0;endq,endh=42,-1
   else:endq,endh=(99 if marker==0 else 93),1
   tests.append((tape,(endq,endh,want)))
 hits=[]
 for w,d,z in product((0,1),(False,True),controls):
  action=w,d,z;works=True;clocks=[]
  for tape,want in tests:
   t=dict(tape);t[0]=w;h=1 if d else -1;state=z
   for n in range(1,limit+1):
    if(state,h,t)==want:clocks.append(n);break
    if state in banned or (state,t.get(h,2))not in R or n==limit:
     works=False;break
    w1,d1,state=R[state,t[h]];t[h]=w1;h+=1 if d1 else -1
   if not works:break
  if works:hits.append({'action':action,'min':min(clocks),'max':max(clocks)})
 results[b]=hits
 print(b,hits,flush=True)
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps({'radius':radius,'max_steps':limit,'forbidden_intermediate':sorted(banned),'branches':results,'machine_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope':'Bounded local restoration paths; no intermediate visits to 83 or 190.'},indent=2)+'\n')
