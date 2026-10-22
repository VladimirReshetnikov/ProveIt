#!/usr/bin/env python3
"""Finite-window positive joins for head-offset state quotients.

Conditional on the closed source invariant, q at head x maps to p at x+h;
other controls map identically. For each invariant q-window, the two paths
must have positive lengths <= K, read only inside that window, and join with
exact tape equality, mapped head and mapped control. This is a finite proof
template, not a search over arbitrary Turing-machine encodings.
"""
from search_elimination import parse
from pathlib import Path
import argparse,json,time,hashlib

def old_trace(t,q,m,r,K):
    state=q;head=0;out=[]
    for steps in range(1,K+1):
        if not -r<=head<=r:break
        bit=(m>>(head+r))&1; row=t.get((state,bit))
        if row is None:break
        w,d,z=row;m=(m&~(1<<(head+r)))|(w<<(head+r));head+=d;state=z
        out.append((state,head,m,steps))
    return out

def join(t,q,p,h,m,r,K,old):
    targets={(p if z==q else z,d+(h if z==q else 0),bits):steps for z,d,bits,steps in old}
    state=p;head=h
    for steps in range(1,K+1):
        if not -r<=head<=r:return None
        bit=(m>>(head+r))&1;row=t.get((state,bit))
        if row is None:return None
        w,d,z=row
        if z==q:d+=h;z=p
        m=(m&~(1<<(head+r)))|(w<<(head+r));head+=d;state=z
        match=targets.get((state,head,m))
        if match is not None:return match,steps
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('invariant');ap.add_argument('--steps',type=int,default=48);ap.add_argument('--out',default='offset_join_results.json');a=ap.parse_args()
    raw=Path(a.table).read_bytes();t=parse(a.table);invraw=Path(a.invariant).read_bytes();inv=json.loads(invraw);r=inv['radius'];masks={int(q):mm for q,mm in inv['masks'].items()};states=sorted(masks);beg=time.time();tested=0;masktests=0;passing=[];best=[];elig=[]
    for q in states:
        if q==0:continue
        dirs={d for (qq,b),(w,d,z) in t.items() if z==q and qq!=q}
        if len(dirs)!=1:continue
        h=-2*next(iter(dirs));elig.append([q,h]);olds={m:old_trace(t,q,m,r,a.steps) for m in masks[q]}
        # Fail-fast order mixes both read-symbol branches and extremes.
        mm=sorted(masks[q],key=lambda m:((m>>r)&1,m));mm=mm[::2]+mm[1::2]
        for p in states:
            if p==q:continue
            tested+=1;cert=[]
            for m in mm:
                masktests+=1;hit=join(t,q,p,h,m,r,a.steps,olds[m])
                if hit is None:break
                cert.append([m,*hit])
            if hit is not None:passing.append({'removed':q,'representative':p,'head_offset':h,'certificate':cert})
            elif len(cert)>=2:best.append({'removed':q,'representative':p,'head_offset':h,'passed':len(cert),'total':len(mm),'failed_mask':m})
    result={'schema':'head-offset-positive-join-v1','input':str(Path(a.table).resolve()),'table_sha256':hashlib.sha256(raw).hexdigest(),'invariant_sha256':hashlib.sha256(invraw).hexdigest(),'radius':r,'maximum_old_and_new_steps':a.steps,'states':len(states),'eligible_removed_states':elig,'ordered_pairs':tested,'window_obligations_tested':masktests,'successes':passing,'partial_matches':sorted(best,key=lambda z:-z['passed'])[:20],'seconds':time.time()-beg}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['eligible_removed_states','successes']},indent=2));print('successes',len(passing))
if __name__=='__main__':main()
