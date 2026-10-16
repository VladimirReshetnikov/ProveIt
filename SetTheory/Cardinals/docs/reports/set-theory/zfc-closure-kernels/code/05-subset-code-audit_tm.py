"""Audit a supplied pinned TM; no third-party machine file is redistributed.

Strong state equivalence means identical writes and directions on each symbol,
with equivalent successor states. It is only one safe optimization class.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

EXPECTED='d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'


def audit(path: Path) -> dict:
    blob=path.read_bytes(); digest=hashlib.sha256(blob).hexdigest()
    if digest != EXPECTED: raise ValueError('This audit is restricted to the pinned 254-state table.')
    trans={}; start=None
    for line in blob.decode('ascii').splitlines():
        if line.startswith('#! start '): start=int(line.split()[-1]); continue
        if not line or line.startswith('#'): continue
        q,r,w,d,t=line.split(); q,r,w,t=map(int,(q,r,w,t))
        if (q,r) in trans: raise ValueError('Duplicate transition.')
        if r not in (0,1) or w not in (0,1) or d not in ('L','R'): raise ValueError('Invalid transition.')
        trans[q,r]=(w,d,t)
    states=sorted({q for q,r in trans}); n=len(states); halt=n
    if states != list(range(n)) or any((q,r) not in trans for q in states for r in (0,1)):
        raise ValueError('Not a total binary machine with contiguous nonhalting states.')
    if any(t not in states+[halt] for w,d,t in trans.values()): raise ValueError('Unexpected target.')
    reach={start}; todo=[start]
    while todo:
        q=todo.pop()
        if q==halt: continue
        for r in (0,1):
            t=trans[q,r][2]
            if t not in reach: reach.add(t); todo.append(t)
    # Monotone refinement: retain the previous class in the refinement key.
    cls={q:0 for q in states}; cls[halt]=1; rounds=0
    while True:
        key_to_id={}; new={}
        for q in states+[halt]:
            key=('halt',) if q==halt else (cls[q],tuple((w,d,cls[t]) for w,d,t in (trans[q,0],trans[q,1])))
            if key not in key_to_id: key_to_id[key]=len(key_to_id)
            new[q]=key_to_id[key]
        rounds+=1
        if len(set(new.values()))==len(set(cls.values())):
            cls=new; break
        cls=new
    groups=defaultdict(list)
    for q in states: groups[cls[q]].append(q)
    roles=Counter()
    for q in states:
        entries=[trans[q,r] for r in (0,1)]
        if all(w==r and d=='R' for r,(w,d,t) in enumerate(entries)): roles['pure_read_right']+=1
        if all(w==r and d=='L' for r,(w,d,t) in enumerate(entries)): roles['pure_read_left']+=1
    return {'table_sha256':digest,'nonhalting_states':n,'transitions':len(trans),'start':start,'halt':halt,
            'graph_reachable_nonhalting_states':len(reach-{halt}),
            'transitions_to_halt':sum(t==halt for w,d,t in trans.values()),
            'strong_bisimulation_classes':len(groups),'refinement_rounds':rounds,
            'nontrivial_merge_classes':[v for v in groups.values() if len(v)>1],
            'syntactic_state_roles':dict(roles),
            'claim_boundary':'No Coq build, Lean proof, semantic-unreachability proof, or global minimality result. Graph reachability is not blank-tape execution reachability.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();result=audit(a.table);text=json.dumps(result,indent=2)+'\n'
    if a.output: a.output.write_text(text)
    print(text,end='')
