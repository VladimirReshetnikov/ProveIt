#!/usr/bin/env python3
"""Bounded optimistic multi-root grammar search; no TM correctness claim."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json,random,time,argparse

SOURCE=Path(__file__).resolve().parents[1]/'search/decoder/closed-sequence-grammar.json'

def attempt(words, seed, mode):
    rng=random.Random(seed)
    words=[list(w) for w in words]
    rules={};pair_id={};nxt=1000
    while True:
        counts=Counter()
        for w in words:
            last={}
            for i,p in enumerate(zip(w,w[1:])):
                if last.get(p,-2)<i-1: counts[p]+=1;last[p]=i
        choices=[(p,n) for p,n in counts.items() if n>=2]
        if not choices:break
        if seed<4: p=max(choices,key=lambda pn:(pn[1],rng.random()))[0]
        else:
            noise=(seed%9)*.13
            p=max(choices,key=lambda pn:(pn[1]-1)*(1+noise*rng.random()))[0]
        node=pair_id.get(p)
        if node is None: node=nxt;nxt+=1;rules[node]=p;pair_id[p]=node
        for j,w in enumerate(words):
            v=[];i=0
            while i<len(w):
                if i+1<len(w) and (w[i],w[i+1])==p:v.append(node);i+=2
                else:v.append(w[i]);i+=1
            words[j]=v
    def intern(a,b):
        nonlocal nxt
        p=(a,b)
        if p not in pair_id:pair_id[p]=nxt;rules[nxt]=p;nxt+=1
        return pair_id[p]
    def build(w):
        if len(w)==1:return w[0]
        if mode=='left':k=len(w)-1
        elif mode=='right':k=1
        elif mode=='balanced':k=len(w)//2
        else:k=rng.randrange(1,len(w))
        return intern(build(w[:k]),build(w[k:]))
    roots=[build(w) for w in words]
    seen=set()
    def visit(v):
        if v in rules and v not in seen:
            seen.add(v)
            for x in rules[v]:visit(x)
    for v in roots:visit(v)
    return len(seen),{str(q):rules[q] for q in sorted(seen)},roots

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=1000);a=ap.parse_args()
    source=json.loads(SOURCE.read_text());out={};began=time.monotonic()
    for field in ('physical','semantic'):
        strings=[source['flattened_'+field+'_words'][str(q)] for q in source['required_entry_roots']]
        atoms=sorted(set(x for w in strings for x in w),key=str);ids={x:i for i,x in enumerate(atoms)}
        words=[[ids[x] for x in w] for w in strings]
        best=None
        for seed in range(a.runs):
            mode=('left','right','balanced','random')[seed%4]
            n,rules,roots=attempt(words,seed,mode)
            if best is None or n<best['states']:
                best=dict(states=n,seed=seed,mode=mode,rules=rules,roots=roots,atoms=atoms)
                print(field,'best',n,'seed',seed,flush=True)
        @lru_cache(None)
        def expand(q):
            if str(q) in best['rules']:
                x,y=best['rules'][str(q)];return expand(x)+expand(y)
            return (best['atoms'][q],)
        assert [list(expand(q)) for q in best['roots']]==strings
        out[field]=best
    result=dict(status='GRAMMAR_ONLY_NOT_A_TM',original_sequence_states=127,entry_roots=source['required_entry_roots'],runs_per_lane=a.runs,seconds=time.monotonic()-began,results=out)
    (Path(__file__).resolve().parents[1]/'results/grammar-search.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',result['seconds'],flush=True)

if __name__=='__main__':main()
