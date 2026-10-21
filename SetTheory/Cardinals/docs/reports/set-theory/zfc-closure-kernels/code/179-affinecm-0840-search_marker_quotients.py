#!/usr/bin/env python3
"""State-specific reversible predecessor-marker encoding for state removal.

Let all retained incoming moves to q be d. Map q at head x to p at head
x+h, optionally toggling tape cell x-d. Then each retained incoming edge
changes its write bit by the same toggle and its direction by h, where
h is 0 or -2*d. Search positive finite-window joins for this exact map.
"""
from search_elimination import parse
from search_offset_joins import old_trace
from pathlib import Path
import argparse,json,time,hashlib

def join(t,q,p,h,side,flip,m,r,K,old):
    targets={}
    for z,hd,bits,steps in old:
        if z==q:
            if flip and not -r<=hd+side<=r:continue
            z=p
            if flip:bits^=1<<(hd+side+r)
            hd+=h
        targets[z,hd,bits]=steps
    state=p;head=h
    if flip:m^=1<<(side+r)
    for steps in range(1,K+1):
        if not -r<=head<=r:return None
        bit=(m>>(head+r))&1;row=t.get((state,bit))
        if row is None:return None
        w,d,z=row
        if z==q:w^=flip;d+=h;z=p
        m=(m&~(1<<(head+r)))|(w<<(head+r));head+=d;state=z
        match=targets.get((state,head,m))
        if match is not None:return match,steps
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('invariant');ap.add_argument('--steps',type=int,default=48);ap.add_argument('--out',default='marker_quotient_results.json');a=ap.parse_args()
    raw=Path(a.table).read_bytes();t=parse(a.table);invraw=Path(a.invariant).read_bytes();inv=json.loads(invraw);r=inv['radius'];masks={int(q):mm for q,mm in inv['masks'].items()};states=sorted(masks);beg=time.time();tested=0;masktests=0;passing=[];best=[];elig=[]
    for q in states:
        if q==0:continue
        dirs={d for (qq,b),(w,d,z) in t.items() if z==q and qq!=q}
        if len(dirs)!=1:continue
        side=-next(iter(dirs));elig.append([q,side]);olds={m:old_trace(t,q,m,r,a.steps) for m in masks[q]}
        mm=sorted(masks[q],key=lambda m:((m>>r)&1,m));mm=mm[::2]+mm[1::2]
        for h,flip in [(0,1),(2*side,1)]:
          for p in states:
            if p==q:continue
            tested+=1;cert=[]
            for m in mm:
                masktests+=1;hit=join(t,q,p,h,side,flip,m,r,a.steps,olds[m])
                if hit is None:break
                cert.append([m,*hit])
            if hit is not None:passing.append({'removed':q,'representative':p,'head_offset':h,'toggle_position':side,'certificate':cert})
            elif len(cert)>=2:best.append({'removed':q,'representative':p,'head_offset':h,'toggle_position':side,'passed':len(cert),'total':len(mm),'failed_mask':m})
    result={'schema':'marker-toggle-positive-join-v1','input':str(Path(a.table).resolve()),'table_sha256':hashlib.sha256(raw).hexdigest(),'invariant_sha256':hashlib.sha256(invraw).hexdigest(),'radius':r,'maximum_old_and_new_steps':a.steps,'states':len(states),'eligible_removed_states':elig,'ordered_quotients':tested,'window_obligations_tested':masktests,'successes':passing,'partial_matches':sorted(best,key=lambda z:-z['passed'])[:30],'seconds':time.time()-beg}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['eligible_removed_states','successes']},indent=2));print('successes',len(passing))
if __name__=='__main__':main()
