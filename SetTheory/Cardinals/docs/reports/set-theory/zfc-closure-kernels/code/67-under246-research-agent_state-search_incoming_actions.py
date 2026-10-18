#!/usr/bin/env python3
"""Bounded discovery of per-incoming-edge instruction replacements."""
import sys,json,time,random,itertools,argparse
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from search_merges import T,Q,SITES,OFFSET,paint,step,lib

LIMIT=500

def collect(edges,cap=16):
    cc={e:[] for e in edges};seen={e:set() for e in edges}
    # Every logical leaf, both decrement branches, varied zero/nonzero values.
    for seed in (1,0,3):
      for pc,kind,r in SITES:
        for pos in ((False,True) if kind=='CD' else (False,)):
            regs=[(i*3+seed)%7 for i in range(9)]
            if kind=='CD':regs[lib.PHYSICAL[r]]=int(pos)*(seed+1)
            target=lib.expected(pc,kind,r,regs,[0],0,40)
            if target:target=(96,target[0]+OFFSET,sum(1<<(x+OFFSET) for x in target[1]))
            c=(96,OFFSET,paint(pc,regs))
            for i in range(4000):
                q,h,t=c
                if q==254:break
                e=(q,(t>>h)&1)
                if e in cc and len(cc[e])<cap:
                    profile=((t>>max(0,h-15))&((1<<31)-1))
                    if profile not in seen[e]:seen[e].add(profile);cc[e].append(c)
                c=step(c)
                if c==target:break
            else:raise ValueError((seed,pc,kind,r,'loop'))
    return cc

def trajectory(c,n=LIMIT):
    initial=c;tt=set();c=step(c)
    for i in range(n):
        if c==initial or c in tt or c[0]==254:break
        tt.add(c);c=step(c)
    if c!=initial:tt.add(c)
    return tt

def patchedstep(c,e,action):
    q,h,t=c
    if q==254:return c
    key=q,(t>>h)&1
    w,d,r=action if key==e else T[key]
    t=(t|(1<<h)) if w else (t&~(1<<h))
    h+=d
    if h<0 or h>2000:return (254,0,-1)
    return r,h,t

def coalesces(c,e,action,tt):
    c=patchedstep(c,e,action);seen=set()
    for i in range(LIMIT):
        if c in tt:return True
        if c in seen or c[0]==254:return False
        seen.add(c);c=patchedstep(c,e,action)
    return False

def main():
    began=time.monotonic()
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('targets',nargs='*',type=int)
    ap.add_argument('--prefix',default='incoming')
    args=ap.parse_args()
    targets=args.targets or [20,109,255,14,7,10,42,75,83,131,112,48,63]
    incoming={q:[e for e,row in T.items() if row[2]==q and e[0]!=q] for q in targets}
    edges={e for es in incoming.values() for e in es}
    cc=collect(edges)
    print('contexts',len(edges),sum(map(len,cc.values())),'seconds',time.monotonic()-began,flush=True)
    actions={};out={}
    for q in targets:
      options={}
      for e in incoming[q]:
        if not cc[e]:raise ValueError(('no witness',e))
        candidates=[(w,d,r) for w in (0,1) for d in (-1,1) for r in Q if r!=q]
        for j,c in enumerate(cc[e]):
            tt=trajectory(c)
            candidates=[a for a in candidates if coalesces(c,e,a,tt)]
            if not candidates:break
        options[str(e)]=candidates
        print('edge',q,e,'survivors',len(candidates),'contexts',j+1,'seconds',time.monotonic()-began,flush=True)
        if len(candidates)<20:print(candidates,flush=True)
      out[q]=dict(incoming=options,combinations=__import__('math').prod(len(v) for v in options.values()))
      (HERE/(args.prefix+'_action_candidates.json')).write_text(json.dumps(out,indent=2))
      print('TARGET',q,'combinations',out[q]['combinations'],flush=True)
    print('DONE',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
