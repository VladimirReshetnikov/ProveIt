#!/usr/bin/env python3
"""Independent literal simulations check a generated window envelope.

These finite samples are an implementation check, not the universal argument.
"""
from pathlib import Path
import argparse,json,random,collections,hashlib
ap=argparse.ArgumentParser();ap.add_argument('machine',type=Path);ap.add_argument('contexts',type=Path)
ap.add_argument('--radius',type=int,default=6);ap.add_argument('--samples',type=int,default=1200)
args=ap.parse_args();K=args.radius
rows={}
for line in (args.machine/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
patterns=collections.defaultdict(set)
for line in args.contexts.read_text().splitlines():
 q,p=map(int,line.split());patterns[q].add(p)
sites=json.loads((args.machine/'sites.json').read_text())
instructions=json.loads((args.machine/'instructions.json').read_text())
rng=random.Random(20261114)
PHY=(6,2,0,4,3,7,8,5,1)
ticks=0;maxsteps=0
for sample in range(args.samples):
 i=sample if sample<min(len(sites),100) else rng.randrange(len(sites))
 path,op,arg=sites[i]
 if not isinstance(path,str):path=''.join(map(str,path))
 vals=[rng.choice([0,1,2,3,7,15]) for _ in range(9)]
 physical=[0]*9
 for r,slot in enumerate(PHY):physical[slot]=vals[r]
 spares=[rng.choice([0,1,2,3,7,15]) for _ in range(rng.randrange(1,7))]
 gap=rng.choice([0,1,2,7,15])
 ones={-1,48+gap}|{j for j,b in enumerate(path) if b=='1'}
 pos=49+gap
 for v in physical+spares:
  pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
 code=instructions[i]
 expected_values=physical.copy();expected_spares=spares.copy();expected_gap=gap
 if code[0]=='inc':
  _,reg,nxt=code;expected_values[PHY[reg]]+=1;expected_spares.append(1)
 elif code[0]=='dec':
  _,reg,z,p=code
  if vals[reg]:expected_values[PHY[reg]]-=1;expected_gap+=1;nxt=p
  else:nxt=z
 elif code[0]=='jump':nxt=code[1]
 else:nxt=None
 expected=None
 if nxt is not None:
  nextpath=sites[nxt][0]
  if not isinstance(nextpath,str):nextpath=''.join(map(str,nextpath))
  expected={-1,48+expected_gap}|{j for j,b in enumerate(nextpath) if b=='1'}
  pos=49+expected_gap
  for v in expected_values+expected_spares:
   pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
 q,head=84,0
 for st in range(200000):
  if st and ((expected is None and q==254) or (q==84 and head==0 and ones==expected)):break
  assert q!=254,('Unexpected sample halt',sample,i,st)
  p=sum(int(head+x in ones)<<(x+K) for x in range(-K,K+1))
  assert p in patterns[q],('Missing literal window',sample,i,st,q,head,p,vals,spares,gap)
  w,d,q=rows[q,int(head in ones)]
  (ones.add if w else ones.discard)(head);head+=d
 else:raise AssertionError(('Sample did not complete',sample,i))
 ticks+=st;maxsteps=max(maxsteps,st)
receipt={'samples':args.samples,'literal_steps':ticks,'maximum_steps':maxsteps,'missing_windows':0,
 'seed':20261114,'radius':K,'table_sha256':hashlib.sha256((args.machine/'machine.native.tm').read_bytes()).hexdigest(),
 'scope':'Implementation regression only; universal coverage is by symbolic affine/list trace envelopes.'}
print(json.dumps(receipt,indent=2))
