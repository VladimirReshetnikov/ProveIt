#!/usr/bin/env python3
"""Recheck the rejected native103 patch from the literal blank configuration."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
b=(HERE/'machine.native.tm').read_bytes();table={}
for line in b.decode().splitlines():
    q,r,w,d,t=line.split();table[int(q),int(r)]=(int(w),1 if d=='R' else -1,int(t))
# Intended seed of the unchanged CS source; complete finite support, head -2.
path='100000';phy=(6,2,0,4,3,7,8,5,1);logical=[2]+[0]*8;physical=[None]*9
for i,j in enumerate(phy):physical[j]=logical[i]
frame=[1]+[int(x) for x in path]+[0]*(48-len(path))+[1]
for v in physical+[1]*26:frame += [0]+[1]*(v+1)
expected={i-3 for i,bit in enumerate(frame) if bit}
ones=set();head=0;state=74;trace=[];seed_seen=False;maximum_ones=0
for steps in range(200000):
    if state==84 and head==-2 and ones==expected:seed_seen=True
    if state==254:break
    bit=int(head in ones);w,d,target=table[state,bit]
    trace.append([state,head,bit,w,d,target])
    if w:ones.add(head)
    else:ones.discard(head)
    head+=d;state=target;maximum_ones=max(maximum_ones,len(ones))
assert state==254 and steps==1361 and head==1 and not seed_seen
assert trace==json.loads((HERE/'trace.json').read_text())
r={'status':'REJECTED','reason':'Literal blank run halts before reaching its intended source seed.',
   'initial_state':74,'initial_head':0,'blank_bit':0,'halt_state':254,'halt_steps':steps,'halt_head':head,
   'table_sha256':hashlib.sha256(b).hexdigest(),'final_one_positions':sorted(ones),
   'trace_sha256':hashlib.sha256((HERE/'trace.json').read_bytes()).hexdigest(),
   'intended_source_seed_seen':seed_seen,'maximum_live_one_count':maximum_ones,'intended_seed_one_count':len(expected),
   'scope':'Independent literal transition simulation; no source-level or arithmetic-box assumptions.'}
(HERE/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
