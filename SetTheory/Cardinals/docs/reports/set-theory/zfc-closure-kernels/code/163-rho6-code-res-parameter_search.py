#!/usr/bin/env python3
"""Exhaustive source-DAG pricing of independent universal-row permutations.

This is a discovery search, not a physical-state allocator or runtime proof.
Default: all 6^7 choices on the original accepted 217 source.
Use --source inputs/upstream216/sites216.compact.json for the partial selector,
or --bundle to add a consistent permutation of the gated bundle and its gate.
Python 3, standard library only; run without -O.
"""
from pathlib import Path
from functools import cache
import argparse, itertools, json, time, sys, hashlib

ROOT = Path(__file__).resolve().parents[2]

def search(source, include_bundle=False):
    rows = json.loads(source.read_text())
    trie = {}
    for path, op, arg in rows:
        at = trie
        for bit in path:
            assert bit in '01' and 'leaf' not in at
            at = at.setdefault(bit, {})
        assert not at
        at['leaf'] = (op, arg)
    ids, nodes = {}, []
    def intern(node):
        if node not in ids:
            ids[node] = len(nodes)
            nodes.append(node)
        return ids[node]
    def decode(at):
        if 'leaf' in at:
            assert set(at) == {'leaf'}
            return intern(at['leaf'])
        assert set(at) == {'0', '1'}
        return intern((decode(at['0']), decode(at['1'])))
    root = decode(trie)
    intervals = [(493,902),(902,1185),(1185,1481),(1481,1780),
                 (1780,2076),(2076,2426),(2426,2657)]
    if include_bundle:
        intervals.append((2657,4604))
    perms = list(itertools.permutations((3,4,5)))
    @cache
    def rename(n, permutation):
        v = nodes[n]
        if isinstance(v[0], str):
            op, arg = v
            return intern((op, permutation[arg-3])) if op in ('CI','CD') and arg in (3,4,5) else n
        return intern((rename(v[0],permutation),rename(v[1],permutation)))
    @cache
    def size(n):
        v=nodes[n]
        return 1 if isinstance(v[0],str) else size(v[0])+size(v[1])
    def pattern(n, lo=0):
        hi=lo+size(n)
        for k,(a,b) in enumerate(intervals):
            if a<=lo and hi<=b:
                return ('variable',k,tuple(rename(n,p) for p in perms))
        if all(hi<=a or b<=lo for a,b in intervals):
            return ('fixed',n)
        v=nodes[n]
        assert not isinstance(v[0],str)
        return ('branch',pattern(v[0],lo),pattern(v[1],lo+size(v[0])))
    template=pattern(root)
    def assemble(p, choices):
        if p[0]=='variable':return p[2][choices[p[1]]]
        if p[0]=='fixed':return p[1]
        return intern((assemble(p[1],choices),assemble(p[2],choices)))
    def cost(n):
        seen=set(); todo=[n]
        while todo:
            k=todo.pop()
            if k in seen:continue
            seen.add(k);v=nodes[k]
            if not isinstance(v[0],str):todo.extend(v)
        return len(seen)
    identity=(0,)*len(intervals)
    assert perms[0]==(3,4,5) and assemble(template,identity)==root
    baseline=cost(root);best=baseline;ties=[];trials=0;start=time.monotonic()
    for choices in itertools.product(range(6),repeat=len(intervals)):
        score=cost(assemble(template,choices));trials+=1
        if score<best:best=score;ties=[]
        if score==best:ties.append(list(choices))
    return {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'trials':trials,'baseline_dag_nodes':baseline,'best_dag_nodes':best,
            'minimum_choices':ties,'permutation_dictionary':perms,
            'intervals':intervals,'seconds':time.monotonic()-start,
            'scope':'Exhaustive only in the specified fixed-tree parameter-permutation family; source DAG pricing, not a physical machine or lower bound.'}

if __name__=='__main__':
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=ROOT/'inputs/upstream217/sites217.json')
    ap.add_argument('--bundle',action='store_true')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();result=search(args.source,args.bundle)
    raw=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(raw)
    print(raw,end='')
