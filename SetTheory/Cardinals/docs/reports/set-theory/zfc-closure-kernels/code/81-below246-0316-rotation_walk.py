#!/usr/bin/env python3
"""Bounded seeded walk through exactly control-equivalent source grammars.

Each accepted rotation preserves all8391 guarded successors. Temporary
increases in distinct pair subtrees are allowed; no binary-state claim.
"""
import json
import random
import math
import time
import rotation_search as r

def main():
    rng=random.Random(20261018);began=time.monotonic()
    ls,cases,by,first=r.a.read_program(r.a.PROGRAM.read_bytes())
    original=r.load(r.a.PROGRAM.read_bytes());initial=r.rotate(original,95,'left')
    best=initial;best_count=202;current=initial;current_count=202
    sequence=[];best_sequence=[];accepted=invalid=checked=0;found=[]
    for trial in range(6000):
        if trial and trial%750==0:
            current=best;current_count=best_count;sequence=list(best_sequence)
        p=rng.choice(r.reachable(current));d=rng.choice(['left','right'])
        candidate=r.rotate(current,p,d)
        if candidate is None:continue
        size=len(r.reachable(candidate))
        if size>best_count+3:continue
        temperature=0.55
        if size>current_count and rng.random()>=math.exp((current_count-size)/temperature):continue
        z=r.check(candidate,ls,cases,set());checked+=1
        if z is None:invalid+=1;continue
        current=candidate;current_count=size;accepted+=1;sequence.append((p,d,size))
        if size<best_count:
            best=candidate;best_count=size;best_sequence=list(sequence)
            z['trial']=trial;z['moves']=best_sequence;z['seed']=20261018
            found.append(z);r.dump_graph(candidate,r.OUT/f'rotation_walk_best_{size}.json',z)
            print(json.dumps({'new_best':size,'trial':trial,'accepted':accepted,'seconds':time.monotonic()-began}),flush=True)
            if size<=199:break
        if trial%250==0:
            print(json.dumps({'trial':trial,'current':size,'best':best_count,'accepted':accepted,'seconds':time.monotonic()-began}),flush=True)
    result={'seed':20261018,'trials':trial+1,'checked':checked,'accepted':accepted,
            'control_rejected':invalid,'best_pair_count':best_count,'improvements':found,
            'seconds':time.monotonic()-began}
    (r.OUT/'rotation_walk_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
