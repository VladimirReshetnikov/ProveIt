#!/usr/bin/env python3
"""Exact all-checkpoint blank startup for the delayed-erasure K230 fold."""
from pathlib import Path
from collections import Counter
import argparse,json,hashlib
from kernels import runtime_support as r
import sys
if not __debug__ or sys.flags.optimize:
 raise RuntimeError('Assertions must be enabled.')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--old',required=True);p.add_argument('--new',required=True);p.add_argument('--output',required=True);p.add_argument('--old-steps',type=int,default=408419);a=p.parse_args()
t=r.table(a.old);n=r.table(a.new);phi=lambda q:71 if q==140 else q
expected={(71,0):5,(140,0):3,(140,1):5,(80,1):9}
qo=qn=95;ho=hn=0;so=set();sn=set();visits=Counter();clock=0;guards=0
for tick in range(a.old_steps):
 assert (phi(qo),ho,so)==(qn,hn,sn),('before',tick,qo,qn,ho,hn)
 b=int(ho in so);row=qo,b
 if row==(140,1):assert ho+1 in so;guards+=1
 visits[row]+=1
 w,d,z=t[row]
 if w:so.add(ho)
 else:so.discard(ho)
 qo,ho=z,ho+d
 duration=expected.get(row,1)
 for _ in range(duration):
  w,d,z=n[qn,int(hn in sn)]
  if w:sn.add(hn)
  else:sn.discard(hn)
  qn,hn=z,hn+d
 clock+=duration
 assert(phi(qo),ho,so)==(qn,hn,sn),('after',tick,qo,qn,ho,hn)
assert(qo,ho,len(so))==(96,-5,351)
assert clock==a.old_steps+sum((d-1)*visits[q,b] for(q,b),d in expected.items())
out={'status':'EXACT_BLANK_STARTUP_ALL_CHECKPOINTS_PASS','old_sha256':sha(a.old),'new_sha256':sha(a.new),'old_steps':a.old_steps,'new_steps':clock,'whole_tape_checkpoints':a.old_steps+1,'exceptional_visits':{f'{q}/{b}':visits[q,b] for q,b in expected},'right_one_guard_visits':guards,'final_state':qn,'head':hn,'one_cells':sorted(sn),'all_other_cells':0}
Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='one_cells'},indent=2))
