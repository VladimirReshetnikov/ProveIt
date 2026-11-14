#!/usr/bin/env python3
"""Exact short ray proof for the rejected parity-scheduler quotient."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'inputs/parity195.native.tm'
rows={}
for line in p.read_text().splitlines():
    q,b,w,d,n=line.split()
    rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
assert len(rows)==390
child={key:(w,d,88 if n==301 else n) for key,(w,d,n) in rows.items() if key[0]!=301}
child[88,0]=(0,-1,51)
child[51,0]=(0,1,122)
assert len(child)==388
q,h,ones=74,0,set()
trace=[]
for step in range(93):
    assert q not in (254,3000)
    bit=int(h in ones)
    w,d,n=child[q,bit]
    trace.append([step,q,h,bit,w,d,n])
    (ones.add if w else ones.discard)(h)
    h+=d;q=n
assert (q,h,ones)==(35,15,{-3,1})
assert child[q,0]==(1,1,q) and h>max(ones)
# For all t>=0, the head is 15+t, the state is35, and every future read is0.
# Each transition writes a1 behind the head and moves to the next fresh zero.
certificate=dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),working_states=194,
    steps=93,state=q,head=h,ones=sorted(ones),outward_row=list(child[q,0]),
    new_scheduler_state_seen=False,trace=trace,
    conclusion='Infinite outward blank ray, proved by induction from this exact configuration.')
print(json.dumps(certificate,indent=2))
