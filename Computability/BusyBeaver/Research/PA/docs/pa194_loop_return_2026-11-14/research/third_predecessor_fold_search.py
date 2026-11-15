#!/usr/bin/env python3
"""Third-predecessor 83/190 fold search with the shared read-one row fixed.

Reproduce both retained receipts from the unpacked archive:
  python3 -B research/third_predecessor_fold_search.py
  python3 -B research/third_predecessor_fold_search.py --kept 190
The input and output can be changed with --machine and --output.
This bounded local search gives no general state-count lower bound.
"""
from pathlib import Path
from itertools import product
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--machine',type=Path,default=ROOT/'machines/PA194LCG/machine.native.tm')
parser.add_argument('--output',type=Path)
parser.add_argument('--kept',type=int,choices=(83,190),default=83)
parser.add_argument('--radius',type=int,default=5)
parser.add_argument('--max-steps',type=int,default=40)
args=parser.parse_args()
assert args.radius>=3 and args.max_steps>=1
base=args.machine
out=args.output or Path(__file__).with_name('third_predecessor_fold_search.json' if args.kept==83 else 'third_predecessor_fold_search_keep190.json')

R={}
for l in base.read_text().splitlines():
 z=l.split()
 if len(z)==5:R[int(z[0]),int(z[1])]=(int(z[2]),z[3]=='R',int(z[4]))
kept=args.kept;removed=190 if kept==83 else 83;radius=args.radius;limit=args.max_steps
assert R[83,1]==R[190,1]==(0,False,42)
controls=sorted({a for a,b in R}-{removed})
R={k:(w,d,kept if z==removed else z) for k,(w,d,z) in R.items() if k[0]!=removed}
tests=[]
for marker in (0,1):
 positions=[i for i in range(-radius,radius+1) if i not in(-3,-2,-1,0)]
 for bits in product((0,1),repeat=len(positions)):
  tape={-3:marker,-2:1,-1:1,0:0,**dict(zip(positions,bits))}
  tests.append((tape,(99 if marker else 93,1,dict(tape))))
hits=[]
for w,d,z in product((0,1),(False,True),controls):
 action=w,d,z;RR=dict(R);RR[kept,0]=action;works=True;clocks=[]
 for tape,want in tests:
  t=dict(tape);h=0;state=kept
  for n in range(limit+1):
   if(state,h,t)==want:clocks.append(n);break
   if (state,t.get(h,2))not in RR or n==limit:works=False;break
   w1,d1,state=RR[state,t[h]];t[h]=w1;h+=1 if d1 else -1
  if not works:break
 if works:
  hit={'action':action,'min':min(clocks),'max':max(clocks)};hits.append(hit);print(hit,flush=True)
print('survivors',len(hits),flush=True)
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps({'radius':radius,'max_steps':limit,'kept':kept,'removed':removed,'contexts':['0110','1110'],'tests':len(tests),'survivors':hits,'machine_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope':'Common read-one row fixed; bounded finite-window search of the read-zero row.'},indent=2)+'\n')
