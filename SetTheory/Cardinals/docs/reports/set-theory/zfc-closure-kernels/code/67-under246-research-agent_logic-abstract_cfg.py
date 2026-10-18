#!/usr/bin/env python3
"""Sound finite-domain dataflow on the exact literal register-program CFG.

The abstract naturals are singleton values 0..K-1 and four disjoint tails
{n>=K : n % 4 == r}.  Join is set union; product joins forget correlations.
This deliberately overapproximates every finite execution from the supplied
root registers.  Results are executable invariant certificates, not sampled
traces.  No remote source or table is modified.
"""
from __future__ import annotations
import argparse
from collections import deque, Counter
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'sources/context246/zfc-context246/sources/Prog254.v'
SOURCE_HASH='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def parse_source():
    data=SOURCE.read_bytes()
    assert hashlib.sha256(data).hexdigest()==SOURCE_HASH
    body=data.decode().split('Definition p254_tab',1)[1].split(':= [',1)[1].split('].',1)[0]
    pat=re.compile(r'\((CN|CI|CD|CB|CC|CH)(?: (\d+))?,\s*(CN|CI|CD|CB|CC|CH)(?: (\d+))?\)')
    nodes=[((a,int(b) if b else None),(c,int(d) if d else None)) for a,b,c,d in pat.findall(body)]
    assert len(nodes)==6459 and not re.sub(r'[\s;]','',pat.sub('',body))
    sites=[]
    def walk(n,p):
        for bit,(op,r) in enumerate(nodes[n]):
            word=p+str(bit)
            if op=='CN': walk(r,word)
            else: sites.append((word,op,r))
    walk(0,'')
    assert len(sites)==6460
    return nodes,sites

def inc(p):
    if not p: return ''
    return f'{(int(p,2)+1)%(1<<len(p)):0{len(p)}b}'

def strip(p,bit,k):
    at=len(p)
    while k and at:
        at-=1
        k-=p[at]==bit
    return p[:at]

def cfg(nodes,sites):
    byword={p:i for i,(p,o,r) in enumerate(sites)}
    def leaf(p):
        q=0; d=0; word=''
        while True:
            b=int(p[d]) if d<len(p) else 0
            word+=str(b); d+=1
            op,r=nodes[q][b]
            if op!='CN': return byword[word]
            q=r
    out=[]
    for p,op,r in sites:
        if op in ('CI','CD'): succ=(leaf(inc(p)),)
        elif op=='CB': succ=(leaf(inc(strip(p,'0',r))),)
        elif op=='CC': succ=(leaf(strip(p,'1',r)),)
        else: succ=()
        if op=='CD': succ+=(leaf(inc(strip(p,'0',1))),)
        out.append(succ)
    return out,leaf('')

class Domain:
    def __init__(self,K):
        assert K>0
        self.K=K
        self.full=(1<<(K+4))-1
        self.nonz=self.full^1
        self.inc_atoms=[]; self.dec_atoms=[]
        for atom in range(K+4):
            if atom<K:
                self.inc_atoms.append(self.exact(atom+1))
                self.dec_atoms.append(0 if atom==0 else self.exact(atom-1))
            else:
                residue=atom-K
                self.inc_atoms.append(1<<(K+(residue+1)%4))
                mask=1<<(K+(residue-1)%4)
                if K%4==residue: mask|=1<<(K-1)
                self.dec_atoms.append(mask)
        self.icache={0:0}; self.dcache={0:0}
    def exact(self,v): return 1<<(v if v<self.K else self.K+v%4)
    def apply(self,mask,atoms,cache):
        if mask not in cache:
            value=0; x=mask
            while x:
                bit=x&-x; x-=bit
                value|=atoms[bit.bit_length()-1]
            cache[mask]=value
        return cache[mask]
    def plus(self,m): return self.apply(m,self.inc_atoms,self.icache)
    def minus(self,m): return self.apply(m,self.dec_atoms,self.dcache)
    def describe(self,m):
        return [a if a<self.K else {'at_least':self.K,'mod4':a-self.K}
                for a in range(self.K+4) if m>>a&1]

def analyze(K,initial):
    nodes,sites=parse_source(); edges,start=cfg(nodes,sites); dom=Domain(K)
    states=[None]*len(sites)
    states[start]=tuple(dom.full if v is None else dom.exact(v) for v in initial)
    work=deque([start]); queued={start}; updates=0; pops=0
    def join(j,new):
        nonlocal updates
        old=states[j]
        merged=new if old is None else tuple(a|b for a,b in zip(old,new))
        if merged!=old:
            states[j]=merged; updates+=1
            if j not in queued: work.append(j); queued.add(j)
    def successors(i,s):
        p,op,r=sites[i]
        if op=='CI':
            out=list(s); out[r]=dom.plus(s[r]); yield edges[i][0],tuple(out)
        elif op=='CD':
            if s[r]&dom.nonz:
                out=list(s); out[r]=dom.minus(s[r]&dom.nonz); yield edges[i][0],tuple(out)
            if s[r]&1:
                out=list(s); out[r]=1; yield edges[i][1],tuple(out)
        elif edges[i]: yield edges[i][0],s
    while work:
        i=work.popleft(); queued.remove(i); pops+=1
        for j,new in successors(i,states[i]): join(j,new)
    # An independent exhaustive post-fixpoint check does not trust worklist order.
    initial_mask=tuple(dom.full if v is None else dom.exact(v) for v in initial)
    assert all(x&~y==0 for x,y in zip(initial_mask,states[start]))
    for i,s in enumerate(states):
        if s is not None:
            assert all(x for x in s)
            for j,new in successors(i,s):
                assert states[j] is not None
                assert all(x&~y==0 for x,y in zip(new,states[j])),(i,j)
    dead=[i for i,s in enumerate(states) if s is None]
    impossible=[]; constant=[]
    for i,(p,op,r) in enumerate(sites):
        s=states[i]
        if s is None: continue
        if op=='CD':
            if not(s[r]&1): impossible.append({'site':i,'path':p,'register':r,'impossible':'zero','abstract':dom.describe(s[r])})
            if not(s[r]&dom.nonz): impossible.append({'site':i,'path':p,'register':r,'impossible':'positive','abstract':dom.describe(s[r])})
        for reg,m in enumerate(s):
            if m.bit_count()==1 and m.bit_length()-1<K:
                constant.append((i,reg,m.bit_length()-1))
    return dict(status='PASS',source_sha256=SOURCE_HASH,domain_K=K,
       tail_modulus=4,initial=initial,working_updates=updates,working_pops=pops,
       leaf_count=len(sites),reachable_leaf_count=len(sites)-len(dead),dead_leaves=dead,
       impossible_decrement_cases=impossible,constant_register_facts=len(constant),
       constant_facts=constant,source_sites=sites,successors=edges,abstract_states=states,
       interpretation='Bits 0..K-1 denote exact singleton values; bits K+r denote n>=K,n%4=r.',
       safety='A checked post-fixpoint containing the exact initial abstract state. Sound primitive update transformers and induction imply every concrete execution is covered.')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--K',type=int,default=8)
    ap.add_argument('--initial',default='3,0,0,0,3,0,0,0,0')
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('abstract_results.json'))
    a=ap.parse_args()
    if not __debug__: ap.error('Assertions required')
    ini=[None if s=='*' else int(s) for s in a.initial.split(',')]
    assert len(ini)==9 and all(x is None or x>=0 for x in ini)
    out=analyze(a.K,ini)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['source_sites','successors','abstract_states','constant_facts']},indent=2))
if __name__=='__main__': main()
