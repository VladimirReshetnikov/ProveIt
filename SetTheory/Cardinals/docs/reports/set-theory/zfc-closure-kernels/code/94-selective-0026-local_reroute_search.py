#!/usr/bin/env python3
"""Exact finite symbolic test of shorter context-dependent router replacement.

Each state branch exposes unknown tape bits explicitly. Acceptance means all
branches reach the exact indicated boundary configuration, preserving the
entire tape, within the finite bound. Failure is only failure of this bounded
search. No finite all-zero simulation is used as a universal premise.
"""
from pathlib import Path
import json,time
import os
BASE=Path(os.environ.get('ZFC245_REFERENCE', str(Path(__file__).resolve().parent.parent/'packages/zfc245-proof-20261018'))).resolve()
T={}
for line in (BASE/'certificate/machine_old.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
states={q for q,b in T}

def prove(replacement,forced,prior,want,bound,forbidden):
    visited=0
    def step(q,h,origin,changes,left):
        nonlocal visited
        visited+=1
        if h==2 and q==want and not changes:return True
        if left==0 or q in forbidden or (q,0) not in T:return False
        if h in changes:bits=[changes[h]]
        elif h in origin:bits=[origin[h]]
        else:bits=[0,1]
        for bit in bits:
            initial=origin if h in origin else {**origin,h:bit}
            write,move,target=T[q,bit]
            new=dict(changes)
            if write==initial[h]:new.pop(h,None)
            else:new[h]=write
            if not step(target,h+move,initial,new,left-1):return False
        return True
    return step(replacement,0,{0:prior,1:forced},{},bound),visited

start=time.monotonic();results=[]
for forced in [0,1]:
    expected=[T[T[166,b][2],forced][2] for b in [0,1]]
    candidates=[]
    for r in sorted(states-{166}):
        if all(prove(r,forced,b,expected[b],12,{166})[0] for b in [0,1]):candidates.append(r)
    result={'removed':166,'written_cell':forced,'target_states':expected,'replacement_states':candidates,'bound':12}
    results.append(result);print(result,flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'results':results,'seconds':time.monotonic()-start},indent=2)+'\n')
