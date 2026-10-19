#!/usr/bin/env python3
"""Exact dictionary parsing over all register-disjoint reorderings of AX.

This is a source experiment, not a binary TM construction.  Its dependency
graph preserves the order of every pair of atoms sharing a register.  A path
in its ideal automaton is therefore a linear extension of that graph.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path
import time


def load(package):
    source = json.loads((package/'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((package/'inputs/semantic-symbols.json').read_text())
    seed = json.loads((package/'grammar.json').read_text())
    ast = source['ast_dag']
    lines = (package/'inputs/semantic.txt').read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    names = {int(q):w for k,w,q in map(str.split, lines[1:n+1])}
    old = {w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split, lines[1:n+1])}
    @cache
    def bounds(i):
        row=ast[i]
        if row[0]=='L':
            op,*xs=row[1]
            return ((1,0) if op=='dec' else (xs[0],0) if op=='brk'
                    else (0,xs[0]) if op=='cont' else (0,0))
        a,b=bounds(row[1]),bounds(row[2])
        return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
    @cache
    def finest(i):
        row=ast[i]
        if row[0]=='N' and bounds(row[1])==bounds(row[2])==(0,0):
            return finest(row[1])+finest(row[2])
        return (i,)
    @cache
    def footprint(i):
        row=ast[i]
        if row[0]=='L':
            return frozenset([row[1][1]]) if row[1][0] in ('inc','dec') else frozenset()
        return footprint(row[1])|footprint(row[2])
    @cache
    def halt_free(i):
        row=ast[i]
        return row[1][0]!='halt' if row[0]=='L' else halt_free(row[1]) and halt_free(row[2])
    ids=sorted({i for name in symbols.values() for i in finest(source['atoms'][name]['ast'])})
    enc={i:chr(65+k) for k,i in enumerate(ids)}
    atoms={c:''.join(enc[i] for i in finest(source['atoms'][name]['ast'])) for c,name in symbols.items()}
    def expand(w):return ''.join(atoms[c] for c in w)
    grammar={w:(l,r) for w,l,r in seed['rules']}
    roots=set(seed['roots'])|{r['word']for r in seed['routes']}
    ax=names[76]
    locks={line.split()[0]for line in(package/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()[1:]}
    fixed=set()
    def freeze(w):
        if len(w)==1 or w in fixed:return
        fixed.add(w)
        for child in grammar[w]:freeze(child)
    for w in (roots-{ax})|locks:freeze(w)
    assert len(fixed)==51
    return dict(source=source,ast=ast,ids=ids,enc=enc,atoms=atoms,expand=expand,
                symbols=symbols,seed=seed,names=names,old=old,grammar=grammar,ax=ax,fixed=fixed,
                footprints={enc[i]:footprint(i)for i in ids},
                closed={enc[i]:bounds(i)==(0,0)for i in ids},
                halt_free={enc[i]:halt_free(i)for i in ids})


def automaton(word,footprints,cap):
    n=len(word)
    last={};pred=[];chains={r:0 for r in range(9)}
    for i,c in enumerate(word):
        regs=footprints[c]
        assert regs,'Zero-footprint atoms need separate occurrence handling.'
        # Repeated predecessors count once, rather than integer addition.
        mask=0
        for r in regs:
            if r in last:mask |= 1<<last[r]
            last[r]=i;chains[r]|=1<<i
        pred.append(mask)
    chains=[mask for mask in chains.values()if mask]
    levels=[[0]];edges={};index={0:0}
    for depth in range(n):
        nxt=set()
        for done in levels[-1]:
            candidates=set()
            for chain in chains:
                remain=chain&~done
                if remain:candidates.add((remain&-remain).bit_length()-1)
            available=[i for i in candidates if pred[i]&done==pred[i]]
            e={}
            for i in available:
                out=done|(1<<i)
                assert word[i]not in e
                e[word[i]]=(out,i)
                nxt.add(out)
            assert e
            edges[done]=e
        levels.append(sorted(nxt))
        for done in nxt:index.setdefault(done,len(index))
        if len(index)>cap:raise RuntimeError(f'Ideal count exceeded cap {cap}')
    assert levels[-1]==[(1<<n)-1]
    return levels,edges,pred


def parse_word(word,dictionary):
    dp=[10**9]*(len(word)+1);dp[-1]=0
    for i in range(len(word)-1,-1,-1):
        dp[i]=min((1+dp[i+len(w)]for w in dictionary if word.startswith(w,i)),default=10**9)
    return dp[0]


def solve(word,footprints,dictionary,cap):
    levels,edges,pred=automaton(word,footprints,cap)
    finish=(1<<len(word))-1
    distance={finish:0};choices={}
    # Trie avoids repeating the same prefix for different dictionary words.
    trie={}
    for w,spelling in dictionary.items():
        node=trie
        for c in w:node=node.setdefault(c,{})
        node['#']=(w,spelling)
    for level in reversed(levels[:-1]):
        for done in level:
            best=10**9;choice=None
            stack=[(done,trie,())]
            while stack:
                state,node,occ=stack.pop()
                if '#'in node and 1+distance[state]<best:
                    best=1+distance[state];choice=(state,*node['#'],occ)
                if state in edges:
                    for c,(target,i)in edges[state].items():
                        if c in node:stack.append((target,node[c],occ+(i,)))
            distance[done]=best
            if choice:choices[done]=choice
    if distance[0]>=10**9:return dict(status='NO_PARSE',ideals=sum(map(len,levels)))
    state=0;spelling=[];order=[];chunks=[]
    while state!=finish:
        out,w,s,occ=choices[state]
        spelling.append(s);order.extend(occ);chunks.append(dict(word=w,spelling=s,occurrences=occ));state=out
    reordered=''.join(word[i]for i in order)
    assert len(set(order))==len(word)==len(order)
    assert all(order.index(i)<order.index(j)for j,p in enumerate(pred)for i in range(len(word))if(p>>i)&1)
    return dict(status='EXACT_OPTIMUM',dictionary_calls=distance[0],
                fixed_order_calls=parse_word(word,dictionary),
                ideals=sum(map(len,levels)),maximum_level_width=max(map(len,levels)),
                fine_word=reordered,coarse_word=''.join(spelling),occurrence_order=order,chunks=chunks,
                distance_certificate={format(s,'x'):d for s,d in distance.items()})


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--cap',type=int,default=1000000)
    ap.add_argument('--modified-source',type=Path)
    ap.add_argument('--variant',default='')
    args=ap.parse_args();started=time.monotonic();m=load(args.package)
    source_word=m['ax']
    if args.modified_source:
        data=json.loads(args.modified_source.read_text())
        if args.variant:
            variants=data.get('variants',{})|data.get('anchored_variants',{})
            data=variants[args.variant]
        source_word=data.get('modified_AX_word',data.get('raw_AX_word'))
    word=m['expand'](source_word)
    assert all(m['closed'][c]and m['halt_free'][c]for c in word)
    small={v:k for k,v in m['atoms'].items()}
    large=small|{m['expand'](w):w for w in m['fixed']}
    results={}
    for name,dictionary in [('coarse_atoms',small),('fixed_core_dictionary',large)]:
        result=solve(word,m['footprints'],dictionary,args.cap)
        result['exact_original_fine_equality']=result.get('fine_word')==word
        results[name]=result
        print(name,{k:v for k,v in result.items()if k not in('fine_word','coarse_word','occurrence_order','chunks','distance_certificate')},flush=True)
    report=dict(status='SOURCE_REORDERING_ONLY',variant=args.variant,
                method='All linear extensions of per-register occurrence orders; exact unit-cost dictionary parsing',
                elapsed_seconds=time.monotonic()-started,
                source_AX_fine_word=word,source_AX_coarse_word=source_word,
                register_footprints={c:sorted(m['footprints'][c])for c in sorted(set(word))},results=results,
                no_machine_claim=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print('elapsed',report['elapsed_seconds'])


if __name__=='__main__':
    assert __debug__
    main()
