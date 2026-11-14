#!/usr/bin/env python3
"""Independently replay the source-invariant/blank-start distinction."""
from pathlib import Path
from collections import deque
import json,hashlib
ROOT=Path(__file__).resolve().parent
old=json.loads((ROOT/'inputs/CSZ.instructions.json').read_text())
new=json.loads((ROOT/'inputs/REJECTED_node1_X.instructions.json').read_text())
def succ(code,pc,m):
    z=code[pc]
    if z[0]=='jump':return [(z[1],m)]
    if z[0]=='inc':return [(z[2],m|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],m&~bit),(z[3],m)] if m&bit else [(z[2],m)]
    assert z[0]=='halt'
    return []
seen={(25,1)};queue=deque(seen)
while queue:
    pc,m=queue.popleft()
    for y in succ(old,pc,m):
        if y not in seen:seen.add(y);queue.append(y)
assert len(seen)==263180 and len(old)==len(new)==3646
changed=[i for i,(a,b)in enumerate(zip(old,new))if a!=b]
assert len(changed)==8
assert all(succ(old,pc,m)==succ(new,pc,m)for pc,m in seen)
rows={}
for line in (ROOT/'inputs/REJECTED_node1_X.native.tm').read_text().splitlines():
    q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
assert len(rows)==388
q=74;h=0;ones=set();trace=[]
for step in range(10000):
    if q==254:break
    bit=int(h in ones);trace.append([q,h,bit]);w,d,q=rows[q,bit]
    (ones.add if w else ones.discard)(h);h+=d
assert q==254 and step==1361
assert not any(q==2066 and b==1 for q,h,b in trace)
print(json.dumps({'source_invariant_pairs':len(seen),'changed_sites':changed,
 'concrete_source_runs_from_clean_seed_agree':True,'blank_halts':True,
 'blank_halting_steps':step,'final_head':h,
 'trace_sha256':hashlib.sha256(json.dumps(trace,separators=(',',':')).encode()).hexdigest()},indent=2))
