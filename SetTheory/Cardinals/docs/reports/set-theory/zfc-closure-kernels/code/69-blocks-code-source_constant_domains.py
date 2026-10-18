#!/usr/bin/env python3
"""Finite constant-domain source invariants for the exact context246 root.

Domain K has atoms {0},...,{K-1},{K,K+1,...}. A mask denotes their union.
Increment shifts bits, saturating at the tail. Positive decrement shifts down
and maps the tail to {K-1} union tail. The source path/operation semantics are
the exact frozen Prog254 semantics used in the preceding invariant audit.
"""
from pathlib import Path
from collections import deque,Counter
import json,time
from program import site_map,lookup

HERE=Path(__file__).resolve().parent
ROOT_VECTOR=(3,0,0,0,3,0,0,0,0)

class Domain:
    def __init__(self,k):
        assert k>=2
        self.k=k;self.tail=1<<k;self.full=(1<<(k+1))-1
        self.initial=tuple(1<<min(n,k) for n in ROOT_VECTOR)
    def inc(self,m):return ((m<<1)&self.full)|(m&self.tail)
    def dec(self,m):return (m>>1)|(m&self.tail)
    def transfers(self,p,vector):
        _,op,r,pos,zero=site_map[p]
        if op=='CH':return
        if op=='CD':
            if vector[r]&1:
                v=list(vector);v[r]=1
                yield lookup(zero)[0],tuple(v),'zero'
            if vector[r]&~1:
                v=list(vector);v[r]=self.dec(vector[r]&~1)
                yield lookup(pos)[0],tuple(v),'positive'
        else:
            v=list(vector)
            if op=='CI':v[r]=self.inc(v[r])
            yield lookup(pos)[0],tuple(v),op
    def solve(self):
        p=lookup('')[0];I={p:self.initial};todo=deque([p]);queued={p};n=0
        while todo:
            p=todo.popleft();queued.remove(p);n+=1
            for q,w,_ in self.transfers(p,I[p]):
                old=I.get(q,(0,)*9);new=tuple(a|b for a,b in zip(old,w))
                if old!=new:
                    I[q]=new
                    if q not in queued:todo.append(q);queued.add(q)
        return I,n
    def check(self,I):
        assert all(a&~b==0 for a,b in zip(self.initial,I[lookup('')[0]]))
        count=0
        for p,v in I.items():
            assert p in site_map and len(v)==9 and all(0<x<=self.full for x in v)
            for q,w,_ in self.transfers(p,v):
                assert q in I and all(a&~b==0 for a,b in zip(w,I[q]))
                count+=1
        return count

def facts(I):
    zeros={(p,r) for p,v in I.items() for r,m in enumerate(v) if m==1}
    dead=set(site_map)-set(I);impossible=set()
    for p,v in I.items():
        _,op,r,_,_=site_map[p]
        if op=='CD':
            if not v[r]&1:impossible.add((p,'zero'))
            if not v[r]&~1:impossible.add((p,'positive'))
    return zeros,dead,impossible

if __name__=='__main__':
    previous=json.loads((HERE.parent/'data/source-abstract-invariant.json').read_text())['invariant']
    z0,d0,g0=facts(previous);summary=[]
    for k in (4,8,16):
        began=time.monotonic();D=Domain(k);I,n=D.solve();checked=D.check(I)
        z,d,g=facts(I)
        record=dict(status='PASS',K=k,initial_root=ROOT_VECTOR,iterations=n,
            checked_transfers=checked,seconds=time.monotonic()-began,
            reachable_leaves=len(I),unreachable_leaves=len(d),impossible_guards=len(g),
            exact_zero_facts=len(z),additional_zero_facts=sorted(z-z0),
            lost_zero_facts=sorted(z0-z),additional_unreachable_leaves=sorted(d-d0),
            additional_impossible_guards=sorted(g-g0))
        (HERE/f'source-constant-domain-{k}.json').write_text(json.dumps(
            dict(**record,invariant={p:list(v) for p,v in sorted(I.items())}),indent=2)+'\n')
        summary.append(record);print(json.dumps(record,indent=2),flush=True)
    (HERE/'source-constant-domain-comparison.json').write_text(json.dumps(summary,indent=2)+'\n')
