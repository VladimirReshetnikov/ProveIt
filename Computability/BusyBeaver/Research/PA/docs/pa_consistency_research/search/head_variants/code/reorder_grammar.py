#!/usr/bin/env python3
"""Free-macro-aware greedy grammar screen of reordered/antecedent-swapped AX.

The result is a source grammar proposal, not a literal consistency machine.
"""
from pathlib import Path
import sys,json,itertools,collections,random,time,heapq
HERE=Path(__file__).resolve().parents[1]/'results'
import grammar as g,permute as p
registry={};defs=[];names=list(g.atoms.values());L=len(names);atomid={n:i for i,n in enumerate(names)}
def pair(a,b):
    k=a,b
    if k not in registry:registry[k]=L+len(defs);defs.append(k)
    return registry[k]
def abstract(t):
    if t in g.atoms:return atomid[g.atoms[t]]
    if not isinstance(t,tuple):return None
    a=abstract(t[0]);b=abstract(t[1]);return None if a is None or b is None else pair(a,b)
free=set()
for t in g.free:
    x=abstract(t)
    if x is not None and x>=L:free.add(x)
def expand(q):return g.nodes.get(names[q],names[q]) if q<L else tuple(map(expand,defs[q-L]))
def count(q):
    seen=set()
    def visit(q):
        if q<L or q in seen:return
        seen.add(q)
        for x in defs[q-L]:visit(x)
    visit(q);return len(seen-free)
assert 92+count(abstract(g.nodes['x67']))==159

def repair(word,seed):
    rng=random.Random(seed);seq=[atomid[x] for x in word];known=free.copy()
    while len(seq)>1:
        raw=collections.Counter(zip(seq,seq[1:]));candidates=[]
        for k,frequency in raw.items():
            if k[0]==k[1]:
                frequency=0;run=0
                for x in seq:
                    if x==k[0]:run+=1
                    else:frequency+=run//2;run=0
                frequency+=run//2
            existing=registry.get(k) in known
            gain=frequency-(0 if existing else 1)
            if gain>0:candidates.append((gain+rng.random()*.35,rng.random(),k))
        if candidates:k=max(candidates)[2]
        else:k=(seq[j:=rng.randrange(len(seq)-1)],seq[j+1])
        symbol=pair(*k);known.add(symbol);new=[];i=0
        while i<len(seq):
            if i+1<len(seq) and (seq[i],seq[i+1])==k:new.append(symbol);i+=2
            else:new.append(seq[i]);i+=1
        seq=new
    return seq[0]

def main():
    variants=[]
    for mask in range(8):
        hs=p.heads.copy()
        for bit,h in enumerate((2,3,5)):
            if mask>>bit&1:
                t=hs[h];hs[h]=p.I(t[2][1],p.I(t[1],t[2][2]))
        variants.append([p.compile(t) for t in hs])
    best=1000;top=[];hist=collections.Counter();start=time.monotonic();tested=0
    for order in itertools.permutations(range(6)):
        for mask,words in enumerate(variants):
            word=p.prefix+sum([words[j] for j in order],[])+p.suffix
            root=repair(word,tested);cost=92+count(root);tested+=1;hist[cost]+=1
            if cost<best:
                best=cost;t=expand(root);assert g.cost(t)==cost
                item=dict(order=[i+1 for i in order],antecedent_mask=mask,internal_nodes=cost,tree=t,word=word)
                (HERE/'reorder_grammar_best.json').write_text(json.dumps(item)+'\n')
                print('BEST',tested,'order',item['order'],'mask',mask,'internal',cost,'seconds',round(time.monotonic()-start,2),flush=True)
            # Keep a small diverse shortlist for exact MILP, with all exact
            # ties retained up to the cap in deterministic encounter order.
            if len(top)<24 or cost<max(x['internal_nodes'] for x in top):
                top.append(dict(order=[i+1 for i in order],antecedent_mask=mask,internal_nodes=cost,word=word,tree=expand(root)))
                top.sort(key=lambda x:x['internal_nodes']);top=top[:24]
        if tested%800==0:print('tested',tested,'best',best,'seconds',round(time.monotonic()-start,2),flush=True)
    (HERE/'reorder_grammar_shortlist.json').write_text(json.dumps(top)+'\n')
    report=dict(words_tested=tested,free_abstract_pair_count=len(free),histogram=dict(hist),best_internal_nodes=best,seconds=time.monotonic()-start,
                scope='Heuristic grammar screen with pre-existing expanded macros free; no physical allocation or runtime proof.')
    (HERE/'reorder_grammar_receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)

if __name__=='__main__':main()
