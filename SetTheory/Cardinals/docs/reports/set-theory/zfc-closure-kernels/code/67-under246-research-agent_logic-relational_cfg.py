#!/usr/bin/env python3
"""Difference-bound inductive invariant for the literal source CFG.

Bounds d[i,j] mean x_i-x_j<=d[i,j], where x_9=0. Joins are
entrywise maxima; addition and guarded decrement are exact zone transformers.
Positive bounds greater than --limit are widened to infinity. Independent
modular masks from abstract_cfg are intersected as proved site invariants.
"""
from __future__ import annotations
import argparse
from collections import deque
import json
from pathlib import Path
import time
from abstract_cfg import parse_source,cfg,Domain

N=10; ZERO=9; INF=10**9

def closure(d,limit):
    a=[list(d[N*i:N*(i+1)]) for i in range(N)]
    for k in range(N):
        row=a[k]
        for i in range(N):
            v=a[i][k]
            if v==INF: continue
            ai=a[i]
            for j in range(N):
                if row[j]==INF: continue
                vv=v+row[j]
                if vv<ai[j]: ai[j]=vv
    if any(a[i][i]<0 for i in range(N)): return None
    return tuple(INF if x>limit else x for row in a for x in row)

def product(initial,limit):
    d=[INF]*(N*N)
    for i in range(N): d[i*N+i]=0
    for i,v in enumerate(initial):
        d[ZERO*N+i]=0 if v is None else -v
        if v is not None: d[i*N+ZERO]=v
    return closure(d,limit)

def shift(d,r,delta,limit):
    out=list(d)
    for i in range(N):
        if i==r: continue
        if out[r*N+i]!=INF: out[r*N+i]+=delta
        if out[i*N+r]!=INF: out[i*N+r]-=delta
    return tuple(INF if x>limit else x for x in out)

def ceil_allowed(mask,lo,K):
    if lo<0: lo=0
    exact=[i for i in range(K) if mask>>i&1 and i>=lo]
    base=max(lo,K)
    tail=[base+(r-base)%4 for r in range(4) if mask>>(K+r)&1]
    return min(exact+tail) if exact or tail else None

def floor_allowed(mask,hi,K):
    if hi==INF:
        if mask>>K: return INF
        return max(i for i in range(K) if mask>>i&1)
    exact=[i for i in range(K) if mask>>i&1 and i<=hi]
    tail=[hi-(hi-r)%4 for r in range(4) if mask>>(K+r)&1 and hi-(hi-r)%4>=K]
    return max(exact+tail) if exact or tail else None

def reduce(d,masks,K,limit):
    if d is None or masks is None: return None
    old=None
    # Closing repeatedly after tightening interval bounds is finite: the domain
    # is the current fixed nonnegative integer polyhedron with modular guards.
    for _ in range(30):
        if d==old: return d
        old=d; out=list(d)
        for r,mask in enumerate(masks):
            lo=ceil_allowed(mask,-d[ZERO*N+r],K)
            hi=floor_allowed(mask,d[r*N+ZERO],K)
            if lo is None or hi is None or lo>hi: return None
            out[ZERO*N+r]=min(out[ZERO*N+r],-lo)
            out[r*N+ZERO]=min(out[r*N+ZERO],hi)
        d=closure(out,limit)
        if d is None: return None
    # An incomplete reduction is still a safe overapproximation.
    return d

def analyze(certificate,limit):
    t=time.monotonic()
    nodes,sites=parse_source(); edges,start=cfg(nodes,sites)
    masks=certificate['abstract_states']; K=certificate['domain_K']
    assert sites==[tuple(x) for x in certificate['source_sites']]
    initial=certificate['initial']
    states=[None]*len(sites)
    states[start]=reduce(product(initial,limit),masks[start],K,limit)
    work=deque([start]); queued={start}; pops=updates=0
    def flow(i,s):
        p,op,r=sites[i]
        if op=='CI': yield edges[i][0],shift(s,r,1,limit)
        elif op=='CD':
            pos=list(s); pos[ZERO*N+r]=min(pos[ZERO*N+r],-1)
            pos=reduce(closure(pos,limit),masks[i],K,limit)
            if pos is not None: yield edges[i][0],shift(pos,r,-1,limit)
            zero=list(s); zero[r*N+ZERO]=min(zero[r*N+ZERO],0)
            zero=reduce(closure(zero,limit),masks[i],K,limit)
            if zero is not None: yield edges[i][1],zero
        elif edges[i]: yield edges[i][0],s
    while work:
        i=work.popleft(); queued.remove(i); pops+=1
        s=reduce(states[i],masks[i],K,limit)
        if s is None: continue
        for j,new in flow(i,s):
            new=reduce(new,masks[j],K,limit)
            if new is None: continue
            old=states[j]
            merged=new if old is None else tuple(max(a,b) for a,b in zip(old,new))
            if old!=merged:
                states[j]=merged; updates+=1
                if j not in queued: work.append(j); queued.add(j)
        if pops%50000==0: print(json.dumps({'progress_pops':pops,'queue':len(work),'seconds':time.monotonic()-t}),flush=True)
    # Prove the final family is inductive by checking every abstract successor.
    for i,s in enumerate(states):
        if s is not None:
            s=reduce(s,masks[i],K,limit)
            if s is None: continue
            for j,new in flow(i,s):
                new=reduce(new,masks[j],K,limit)
                if new is not None:
                    assert states[j] is not None
                    assert all(a<=b for a,b in zip(new,states[j])),(i,j)
    impossible=[]; dead=[]; equalities=[]
    for i,s in enumerate(states):
        s=reduce(s,masks[i],K,limit)
        if s is None: dead.append(i); continue
        p,op,r=sites[i]
        if op=='CD':
            if s[r*N+ZERO]==0: impossible.append({'site':i,'path':p,'register':r,'impossible':'positive'})
            if s[ZERO*N+r]<0: impossible.append({'site':i,'path':p,'register':r,'impossible':'zero'})
        for r in range(9):
            for z in range(r+1,10):
                if s[r*N+z]!=INF and s[r*N+z]==-s[z*N+r]:
                    equalities.append((i,r,z,s[r*N+z]))
    return dict(status='PASS',kind='Difference-bound zones intersected with existing modular invariant',
      source_sha256=certificate['source_sha256'],mask_domain_K=K,positive_bound_limit=limit,
      initial=initial,seconds=time.monotonic()-t,pops=pops,updates=updates,
      dead_leaves=dead,impossible_decrement_cases=impossible,equalities=equalities,
      abstract_zones=states,source_sites=sites,
      zone_format='Flat10x10;d[i,j] means xi-xj<=d[i,j];x9=0;1000000000=infinity. Each site is intersected with the source mask family.')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mask-certificate',type=Path,default=Path(__file__).with_name('abstract_k8.json'))
    ap.add_argument('--limit',type=int,default=8)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('relational_results.json'))
    a=ap.parse_args()
    if not __debug__: ap.error('Assertions required')
    out=analyze(json.loads(a.mask_certificate.read_text()),a.limit)
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['equalities','abstract_zones','source_sites']},indent=2))
if __name__=='__main__': main()
