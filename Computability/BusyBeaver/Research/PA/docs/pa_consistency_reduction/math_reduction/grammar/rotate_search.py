#!/usr/bin/env python3
"""Local associativity search for a smaller shared binary parse of AX."""
from pathlib import Path
import random, json, time, sys, math
from search_grammar import DEFS,TOKENS,WORD

def tree(t):
    if isinstance(t,str):
        if t in TOKENS:return TOKENS[t]
        return tree(DEFS[t])
    a,b=t
    if a == '.inc' and b == 1:return 'i'
    if a == '.breakTo' and b == 1:return 'B'
    assert not (isinstance(a,str) and a.startswith('.')),t
    return tree(a),tree(b)

def nodes(t):
    seen=set()
    def go(q):
        if not isinstance(q,tuple) or q in seen:return
        seen.add(q);go(q[0]);go(q[1])
    go(t)
    return seen

def paths(t,p=()):
    if not isinstance(t,tuple):return []
    return [(p,t)]+paths(t[0],p+(0,))+paths(t[1],p+(1,))

def replace(t,key,val):
    if t==key:return val
    if not isinstance(t,tuple):return t
    return replace(t[0],key,val),replace(t[1],key,val)

def replace_one(t,p,val):
    if not p:return val
    a,b=t
    if p[0]==0:return replace_one(a,p[1:],val),b
    return a,replace_one(b,p[1:],val)

def expand(t):
    if isinstance(t,str):return [t]
    return expand(t[0])+expand(t[1])

def output(t,path):
    rules={};rev={}
    def go(q):
        if isinstance(q,str):return q
        if q in rev:return rev[q]
        a,b=map(go,q);n=f'r{len(rules)}';rev[q]=n;rules[n]=(a,b)
        return n
    root=go(t)
    data={'nodes':len(rules),'root':root,'rules':rules,'tokens':TOKENS,'word':WORD}
    path.write_text(json.dumps(data,indent=2))

if __name__=='__main__':
    rng=random.Random(723);base=tree('x67');best=len(nodes(base));besttree=base
    assert expand(base)==WORD
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 100000
    t=base;score=best;start=time.time()
    print('baseline',best,flush=True)
    for it in range(budget):
        if it%20000==0:t=besttree;score=best
        ps=paths(t)
        p,q=rng.choice(ps)
        a,b=q
        if rng.randrange(2):
            if not isinstance(a,tuple):continue
            u,v=a;new=(u,(v,b))
        else:
            if not isinstance(b,tuple):continue
            u,v=b;new=((a,u),v)
        cand=replace(t,q,new) if rng.random()<.6 else replace_one(t,p,new)
        s=len(nodes(cand));delta=s-score
        temp=.4*(1-(it%20000)/20000)+.05
        if delta<=0 or rng.random()<math.exp(-delta/temp):t=cand;score=s
        if s<best:
            best=s;besttree=cand;assert expand(cand)==WORD
            output(cand,Path(__file__).with_name('rotate_best.json'))
            print('best',best,'iter',it,'secs',round(time.time()-start,3),flush=True)
    print('done',best,'secs',round(time.time()-start,3),flush=True)
