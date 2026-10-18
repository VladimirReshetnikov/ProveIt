#!/usr/bin/env python3
"""Discovery only: directed state identifications on exact sampled contexts."""
import sys, json, random, time
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]/'sources/context246/zfc-context246'
sys.path.insert(0,str(BASE/'code'))
import check_literal_instructions as lib

T=lib.read_table(BASE/'machine/zfc_prefix246_old.tm')
Q=sorted({q for q,b in T})
SITES=lib.program_sites(BASE/'sources/Prog254.v')
OFFSET=100

def paint(pc,regs,spares=[0]):
    return sum(1<<(x+OFFSET) for x in lib.paint(pc,40,regs,spares,0))

def step(c,remove=None,replace=None):
    q,h,t=c
    if q==254:return c
    if q==remove:q=replace
    w,d,r=T[q,(t>>h)&1]
    t=(t|(1<<h)) if w else (t&~(1<<h))
    h+=d
    if h<0 or h>2000:return (254,0,-1)
    if r==remove:r=replace
    return (r,h,t)

def contexts():
    """Keep up to 20 distinct local profiles per state to screen merges."""
    cc={q:[] for q in Q}; pp={q:set() for q in Q}
    for pc,kind,r in SITES:
        for pos in ((False,True) if kind=='CD' else (False,)):
            regs=[1]*9
            if kind=='CD':regs[lib.PHYSICAL[r]]=int(pos)
            target=lib.expected(pc,kind,r,regs,[0],0,40)
            if target:
                target=(96,target[0]+OFFSET,sum(1<<(x+OFFSET) for x in target[1]))
            c=(96,OFFSET,paint(pc,regs))
            for i in range(2000):
                q,h,t=c
                if q==254:break
                p=(t>>(h-12))&((1<<25)-1)
                if len(cc[q])<20 and p not in pp[q]:
                    pp[q].add(p);cc[q].append(c)
                c=step(c)
                if c==target:break
            else:raise ValueError((pc,kind,r,'loop'))
    return cc

def trajectories(c,n=800):
    tt=set()
    for i in range(n):
        if c in tt or c[0]==254:break
        tt.add(c);c=step(c)
    tt.add(c)
    return tt

def coalesce(c,q,r,tt,limit=800):
    seen=set();c=(r,c[1],c[2])
    for i in range(limit):
        if c in tt:return True
        if c in seen or c[0]==254:return False
        seen.add(c);c=step(c,q,r)
    return False

def main():
    began=time.monotonic();cc=contexts()
    print('contexts',sum(map(len,cc.values())),[q for q,v in cc.items() if not v],flush=True)
    candidates=[(q,r) for q in Q for r in Q if q!=r and q!=96]
    for rank in range(20):
        new=[]
        ts={q:trajectories(v[rank]) for q,v in cc.items() if len(v)>rank}
        for q,r in candidates:
            if len(cc[q])<=rank or coalesce(cc[q][rank],q,r,ts[q]):new.append((q,r))
        candidates=new
        print('rank',rank,'survivors',len(candidates),'seconds',time.monotonic()-began,flush=True)
        if len(candidates)<30:print(candidates,flush=True)
        (Path(__file__).parent/'merge_candidates.json').write_text(json.dumps(candidates))
        if not candidates:break

if __name__=='__main__':main()
