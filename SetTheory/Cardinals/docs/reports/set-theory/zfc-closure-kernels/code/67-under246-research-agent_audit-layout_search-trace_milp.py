#!/usr/bin/env python3
"""Shared grammar MILP modulo disjoint closed-routine commutation.

Every possible factorization of each dictionary trace is enumerated through
the order ideals of its register-dependence poset. This permits a grammar rule
AB whose concrete order differs from the old word, but only by swaps of
CH-free closed atoms with disjoint register footprints.
"""
import argparse,random,sys
from collections import deque
from functools import lru_cache
import dictionary_milp as d
import trace_grammar as t

t.affine_enabled='--affine' in sys.argv
visit,root=t.normalize(d.g.original,d.g.original_root)
d.labels=t.labels;d.interned=t.interned
d.cache={e:visit(e) for e in [('N',n) for n in d.g.original]+[e for p in d.g.original.values() for e in p if e[0]!='N']}
d.canonical_root=root
d.oldwords={v[1] for v in d.labels.values() if v[0]=='S'}
d.oldsplit={}
for n,p in d.g.original.items():
    k=d.labels[d.cache['N',n]]
    if k[0]=='S':
        sides=[]
        for e in p:
            i=d.cache[e];child=d.labels[i]
            sides.append(child[1] if child[0]=='S' else (i,))
        d.oldsplit[k[1]]=tuple(sides)
d.required={d.labels[x][1] for k in d.labels.values() if k[0]=='A' for x in k[1:] if d.labels[x][0]=='S'}
if d.labels[root][0]=='S':d.required.add(d.labels[root][1])
d.normalize_word=t.trace_normal
d.grammar_kind='closed_CH_free_disjoint_register_trace'
d.output_prefix='trace_dictionary'
if t.affine_enabled:
    d.output_prefix='trace_affine_dictionary'
    d.grammar_kind='closed_disjoint_or_certified_total_affine_trace'

@lru_cache(None)
def factorizations(w):
    """Enumerate all nonempty proper order ideals as trace left factors."""
    pred=t.dependence_predecessors(w)
    masks=[sum(1<<j for j in ps) for ps in pred]
    successors=[[] for _ in w]
    for i,ps in enumerate(pred):
        for j in ps:successors[j].append(i)
    start=tuple(i for i,ps in enumerate(pred) if not ps)
    todo=deque([(0,start)]);seen={0};factors=set()
    full=(1<<len(w))-1
    while todo:
        mask,ready=todo.popleft()
        if mask and mask!=full:
            a=tuple(x for i,x in enumerate(w) if mask>>i&1)
            b=tuple(x for i,x in enumerate(w) if not mask>>i&1)
            a,b=t.trace_normal(a),t.trace_normal(b)
            assert t.trace_normal(a+b)==w
            factors.add((a,b))
        for i in ready:
            newmask=mask|1<<i
            if newmask in seen:continue
            seen.add(newmask)
            newready=[j for j in ready if j!=i]
            newready.extend(j for j in successors[i] if not masks[j]&~newmask)
            todo.append((newmask,tuple(sorted(set(newready)))))
    return tuple(sorted(factors))

_trie_cache={}
def split_word(w,dictionary):
    """Enumerate dictionary factors directly through a prefix trie.

    An exact left factor is an order ideal.  Its canonical word can be read
    using only currently minimal occurrences in the dependence graph.  This
    trie traversal therefore has the same answers as all ideal enumeration,
    while avoiding construction of ideals that are not dictionary phrases.
    """
    key=id(dictionary)
    if key not in _trie_cache:
        trie=[dict(children={},word=None)]
        vocabulary=set(dictionary)|{(x,) for v in dictionary for x in v}
        for word in vocabulary:
            at=0
            for x in word:
                if x not in trie[at]['children']:
                    trie[at]['children'][x]=len(trie);trie.append(dict(children={},word=None))
                at=trie[at]['children'][x]
            trie[at]['word']=word
        _trie_cache[key]=trie
    trie=_trie_cache[key]
    pred=t.dependence_predecessors(w)
    masks=[sum(1<<j for j in ps) for ps in pred]
    successors=[[] for _ in w]
    for i,ps in enumerate(pred):
        for j in ps:successors[j].append(i)
    start=tuple(i for i,ps in enumerate(pred) if not ps)
    full=(1<<len(w))-1;found=set();todo=[(0,0,start)]
    while todo:
        at,mask,ready=todo.pop()
        a=trie[at]['word']
        if a is not None and mask!=full:
            b=t.trace_normal(tuple(x for i,x in enumerate(w) if not mask>>i&1))
            if len(b)==1 or b in dictionary:
                assert t.trace_normal(a+b)==w
                found.add((a,b))
        for i in ready:
            if w[i] not in trie[at]['children']:continue
            newmask=mask|1<<i
            newready=[j for j in ready if j!=i]
            newready.extend(j for j in successors[i] if not masks[j]&~newmask)
            todo.append((trie[at]['children'][w[i]],newmask,tuple(sorted(set(newready)))))
    return sorted(found)
d.split_word=split_word

def random_order(w,rng):
    pred=t.dependence_predecessors(w)
    succ=[[] for _ in w];degree=list(map(len,pred))
    for i,ps in enumerate(pred):
        for p in ps:succ[p].append(i)
    ready=[i for i,n in enumerate(degree) if not n];result=[]
    while ready:
        k=rng.randrange(len(ready));i=ready.pop(k);result.append(w[i])
        for j in succ[i]:
            degree[j]-=1
            if not degree[j]:ready.append(j)
    assert t.trace_normal(tuple(result))==w
    return tuple(result)

def enrich_dictionary(orders,maxlen):
    """Collect trace factors from reproducible alternative linearizations."""
    rng=random.Random(203246)
    for word in d.required:
        for trial in range(orders):
            w=random_order(word,rng)
            for size in range(2,min(maxlen,len(w))+1):
                for i in range(len(w)-size+1):
                    d.extra_words.add(t.trace_normal(w[i:i+size]))
    print('ENRICHED',len(d.extra_words),'trace phrases',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--maxlen',type=int,default=12);ap.add_argument('--minfreq',type=int,default=2)
    ap.add_argument('--maxzeros',type=int,default=7);ap.add_argument('--maxdepth',type=int,default=39)
    ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--freeze',default='')
    ap.add_argument('--seed-shortzero',action='store_true');ap.add_argument('--node-price',action='store_true')
    ap.add_argument('--orders',type=int,default=0)
    ap.add_argument('--affine',action='store_true')
    a=ap.parse_args()
    if a.orders:
        enrich_dictionary(a.orders,a.maxlen)
        d.output_prefix+=f'_orders{a.orders}'
    d.run(a.maxlen,a.minfreq,a.seconds,a.maxzeros,a.maxdepth,True,a.seed_shortzero,not a.node_price,
          tuple(map(int,a.freeze.split(','))) if a.freeze else ())
