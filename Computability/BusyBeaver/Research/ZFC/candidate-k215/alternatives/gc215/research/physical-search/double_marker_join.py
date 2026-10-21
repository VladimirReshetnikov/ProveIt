#!/usr/bin/env python3
"""Two conditional origin folds with positive joining of both executions."""
from local_invariants import read
from pathlib import Path
import argparse,json,time,itertools

def run(T,provider,origin,mask,r,cap,mp,forbidden):
    b=mask>>r&1;w,d,t=T[origin,b];target=mp.get(t,t)
    goals=set();old_tape=mask;old_state=origin;old_head=0
    for oldstep in range(1,cap+1):
        j=old_head+r
        if not 0<=j<=2*r or (old_state,(old_tape>>j)&1) not in T:break
        ow,od,oz=T[old_state,(old_tape>>j)&1]
        old_tape=(old_tape&~(1<<j))|(ow<<j);old_head+=od;old_state=oz
        goals.add((mp.get(old_state,old_state),old_head,old_tape))
    tape=mask;state=provider;head=0
    for step in range(1,cap+1):
        if state in forbidden:return False
        j=head+r
        if not 0<=j<=2*r or (state,(tape>>j)&1) not in T:return False
        bit=tape>>j&1;w,move,z=T[state,bit]
        tape=(tape&~(1<<j))|(w<<j);head+=move;state=mp.get(z,z)
        if (state,head,tape) in goals:return step
    return False

def search(T,start,inv,cap=64):
    pairs=inv['distinguishable_pairs'];r=inv['radius'];masks={int(q):ms for q,ms in inv['masks'].items()};states=sorted(masks);hits=[];attempts=0;clock=time.monotonic()
    for a,c in itertools.combinations(pairs,2):
        if a['side']!=c['side'] or a['branch']==c['branch']:continue
        origins={a['p'],a['q'],c['p'],c['q']}
        if len(origins)!=4 or start in origins:continue
        # Keep p for both. No old role in this set is used internally by a macro.
        mp={a['q']:a['p'],c['q']:c['p']};providers=[];cert=[]
        for marker in (0,1):
            tests=[]
            for e in (a,c):
                o=e['p'] if e['pmarker']==marker else e['q']
                tests.extend((o,m) for m in masks[o] if m>>r&1==e['branch'])
            found=[]
            for provider in states:
                if provider in origins:continue
                attempts+=1;dur=[]
                for o,m in tests:
                    z=run(T,provider,o,m,r,cap,mp,origins)
                    if not z:break
                    dur.append(z)
                else:found.append({'state':provider,'durations':sorted(set(dur)),'cases':len(tests)})
            providers.append(found)
            if not found:break
        if len(providers)==2 and all(providers):
            h={'pair0':a,'pair1':c,'providers':providers};hits.append(h);print('HIT',h,flush=True)
    return {'hits':hits,'attempts':attempts,'seconds':time.monotonic()-clock,'radius':r,'cap':cap}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('invariant');ap.add_argument('--out',required=True);ap.add_argument('--cap',type=int,default=64);a=ap.parse_args()
    T,start=read(a.table);inv=json.loads(Path(a.invariant).read_text());x=search(T,start,inv,a.cap);Path(a.out).write_text(json.dumps(x,indent=2)+'\n');print(x)
