#!/usr/bin/env python3
"""Indexed synthesis of two-row folds with bounded unchanged helper fragments.

See ../reduction_section.tex for the mathematical specification. This version builds
an index of all finite local blocks first, then intersects their actions over
every abstractly admitted entry window. Each path records its internal
controls; a folded control may only be entered at the last step.
"""
from window_fold_search import parse,abstract
from itertools import combinations
from pathlib import Path
from collections import defaultdict
import json,argparse,time,hashlib

def index_blocks(t,qs,k,limit):
    idx=defaultdict(list);width=2*k+1;center=1<<k
    actions=[(w,d,z)for w in[0,1]for d in[-1,1]for z in qs+[254]]
    for bits in range(1<<width):
        for aid,(w,d,q)in enumerate(actions):
            h=d;v=(bits&~center)|(w<<k);internal=set();found=set()
            for n in range(1,limit+1):
                if h in(-1,1)and(v&~center)==(bits&~center):
                    key=(bits,(v>>k)&1,h,q)
                    if key not in found:
                        idx[key].append((aid,n,frozenset(internal)));found.add(key)
                if not -k<=h<=k:break
                row=t.get((q,(v>>(h+k))&1))
                if row is None:break
                internal.add(q)
                w,d,q=row;v=(v&~(1<<(h+k)))|(w<<(h+k));h+=d
    return actions,idx

def search(path,k,limit,out):
    begin=time.time();start,t=parse(path);qs=sorted({q for q,b in t});windows,n=abstract(t,start,k)
    actions,idx=index_blocks(t,qs,k,limit);print('indexed',len(idx),'keys',flush=True)
    paircount=0;survivors=[];branches=0
    cases={q:[sorted(v for v in windows[q]if(v>>k)&1==c)for c in[0,1]]for q in qs}
    for a,b in combinations(qs,2):
        if b==start:a,b=b,a
        paircount+=1;phi=lambda q:a if q==b else q
        # Do not reject overlapping windows with different old one-step outputs:
        # a common new trajectory may match the two targets at different times.
        choices=[]
        for c in[0,1]:
            branches+=1;ok=None;durations={};examplecount=0
            for i in range(max(len(cases[a][c]),len(cases[b][c]))):
                for oldq in[a,b]:
                    if i>=len(cases[oldq][c]):continue
                    bits=cases[oldq][c][i];w,d,z=t[oldq,c];zs=[a,b]if z in(a,b)else[z]
                    valid={}
                    for zz in zs:
                        for aid,nsteps,internal in idx.get((bits,w,d,zz),[]):
                            if actions[aid][2]==b or a in internal or b in internal:continue
                            valid[aid]=min(valid.get(aid,limit+1),nsteps)
                    ok=set(valid) if ok is None else ok&valid.keys();examplecount+=1
                    for aid in ok:durations.setdefault(aid,[]).append(valid[aid])
                    if not ok:break
                if not ok:break
            if ok is None:ok={i for i,act in enumerate(actions)if act[2]!=b}
            choices.append([{'action':actions[aid],'cases':examplecount,'min_duration':min(durations.get(aid,[0])),'max_duration':max(durations.get(aid,[0]))}for aid in sorted(ok)])
            if not ok:break
        if len(choices)==2 and all(choices):
            survivors.append({'keep':a,'remove':b,'choices':choices});print('SURVIVOR',a,b,flush=True)
    r={'machine_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),'start':start,'radius':k,'step_bound':limit,'abstract_states':n,'all_pairs':paircount,'overlap_screen':False,'branches_considered':branches,'provider_actions_per_branch':len(actions)-4,'survivors':survivors,'seconds':time.time()-begin,'scope':'Two-row folds under projection b->a; every row write/move/existing-state action considered via indexed local blocks; unchanged provider fragment; no internal visits to either merged state; no read beyond the 2k+1-cell window. No overlap-screen restriction: different old targets may be matched at different positive times. All initial tapes at the declared start control. Finite search result, not a global lower bound.'}
    toolroot=Path(__file__).resolve().parent
    r['implementation_sha256']={name:hashlib.sha256((toolroot/name).read_bytes()).hexdigest()for name in['indexed_fold_search.py','window_fold_search.py']}
    Path(out).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('machine');p.add_argument('--radius',type=int,default=3);p.add_argument('--steps',type=int,default=32);p.add_argument('--out',default='indexed-search.json');a=p.parse_args();search(a.machine,a.radius,a.steps,a.out)
