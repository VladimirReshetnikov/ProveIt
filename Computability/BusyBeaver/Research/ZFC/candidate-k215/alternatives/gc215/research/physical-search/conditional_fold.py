#!/usr/bin/env python3
"""One-row state folding under a finite inductive local-tape invariant."""
from local_invariants import read
from pathlib import Path
import argparse,json,time,itertools

def check(T,p,q,origin,mask,r,cap,patch):
    b=(mask>>r)&1
    w,d,target=T[origin,b]
    if target==q:target=p
    expect=(mask&~(1<<r))|(w<<r)
    tape=mask;state=p;head=0
    for step in range(1,cap+1):
        j=head+r
        if not 0<=j<=2*r:return False
        bit=tape>>j&1
        tr=patch if state==p and bit==patch[3] else T.get((state,bit))
        if tr is None:return False
        w,move,z=tr[:3]
        tape=(tape&~(1<<j))|(w<<j);head+=move;state=p if z==q else z
        if (state,head,tape)==(target,d,expect):return step
    return False

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('invariant');ap.add_argument('--out',required=True);ap.add_argument('--cap',type=int,default=64);a=ap.parse_args()
    T,start=read(a.table);inv=json.loads(Path(a.invariant).read_text());r=inv['radius'];masks={int(q):ms for q,ms in inv['masks'].items()};states=sorted(masks);hits=[];clock=time.monotonic();attempts=0;passes=0
    for p,q in itertools.permutations(states,2):
        if q==start:continue
        for b in (0,1):
            def ren(tr):
                w,d,t=tr;return w,d,p if t==q else t
            if ren(T[p,1-b])!=ren(T[q,1-b]):continue
            a0=[m for m in masks[p] if m>>r&1==b]; a1=[m for m in masks[q] if m>>r&1==b]
            tests=[]
            for k in range(max(len(a0),len(a1))):
                if k<len(a0):tests.append((p,a0[k]))
                if k<len(a1):tests.append((q,a1[k]))
            for w,d,t in itertools.product((0,1),(-1,1),states+[254]):
                if t==q:continue
                patch=(w,d,t,b);attempts+=1;times=[]
                for origin,m in tests:
                    z=check(T,p,q,origin,m,r,a.cap,patch)
                    if not z:break
                    times.append(z)
                else:
                    hits.append({'keep':p,'delete':q,'read':b,'row':[w,d,t],'cases':len(tests),'durations':sorted(set(times))});print(hits[-1],flush=True)
    result={'hits':hits,'seconds':time.monotonic()-clock,'radius':r,'cap':a.cap,'attempts':attempts,'states':len(states),'scope':'Original reachable-window invariant, exact positive macro simulation for all masks with no exterior read; one branch changed and all incoming delete labels redirected.'}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(result)
if __name__=='__main__':main()
