#!/usr/bin/env python3
"""Construct and check a direct reversed-implication readDCons macro.

This is a local source routine only; it is not a compiled consistency TM.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

import source_core as scan

def pair(a,b): return (a+b)*(a+b+1)//2+b
def run(tree, regs, limit=1000000):
    graph = scan.graph(tree)
    r = list(regs)
    pc = 0
    steps = 0
    while pc is not None:
        if steps == limit:
            raise RuntimeError('finite control test exceeded limit')
        ins = graph[pc]
        if ins[0] == 'inc':
            r[ins[1]] += 1
            pc = ins[2]
        elif ins[0] == 'dec':
            if r[ins[1]]:
                r[ins[1]] -= 1
                pc = ins[3]
            else:
                pc = ins[2]
        elif ins[0] == 'jump':
            pc = ins[1]
        else:
            raise RuntimeError('unexpected halt inside closed macro')
        steps += 1
    return r, steps

def export(tree):
    t = scan.store[tree]
    if t[0] == 'node':
        return [export(t[1]), export(t[2])]
    return ['leaf', t[0], t[1]]

def bracketings(xs):
    if len(xs) == 1:
        yield xs[0]
    for i in range(1,len(xs)):
        for a in bracketings(xs[:i]):
            for b in bracketings(xs[i:]):
                yield scan.node(a,b)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    dec4 = scan.interned(('dec',4))
    dec7 = scan.interned(('dec',7))
    # node40 increments r7 then r6; node52 increments r4 then continues.
    copy = scan.node(scan.node(dec4, scan.env['node40']),
                     scan.node(dec7, scan.env['node52']))
    assert scan.bound(copy) == (0,0)
    variants = list(bracketings([scan.env['node32'], scan.env['node53'],
                                copy, scan.env['node64']]))
    records = []
    for new in variants:
        assert scan.bound(new) == (0,0)
        changed = scan.rewrite(scan.root,scan.env['node75'],new)
        records.append({'source_internal_nodes':scan.metric(changed),
                        'macro_internal_nodes':scan.metric(new),
                        'macro_sites':len(list(scan.leaf_occurrences(new))),
                        'source_sites':len(list(scan.leaf_occurrences(changed))),
                        'tree':export(new)})
    new = variants[0]
    tests = 0
    largest = 0
    for t,d,x,tail in itertools.product(range(5), range(5), range(4), range(4)):
        inp = [9,t,13,7,d,11,0,0,pair(x,tail),17]
        old, no = run(scan.env['node75'],inp)
        actual, nn = run(new,inp)
        expected = list(inp)
        expected[1] = 4*pair(d+x,t)
        expected[4] = d+x
        expected[8] = tail
        assert actual == expected,(inp,actual,expected)
        expected[1] = 4*pair(t,d+x)
        assert old == expected,(inp,old,expected)
        tests += 1
        largest = max(largest,no,nn)
    occurrences=[]
    leaves=list(scan.leaf_occurrences(scan.root))
    for path,tree in scan.node_occurrences(scan.root):
        if tree==scan.env['node75']:
            indices=[i for i,(q,_) in enumerate(leaves) if q[:len(path)]==path]
            occurrences.append({'path':list(path),'entry':min(indices),'exit':max(indices)+1})
    result={'scope':'Local all-natural source contract with finite transcription checks; no full I-transposed source or binary TM.',
            'input_sha256':hashlib.sha256(scan.raw).hexdigest(),
            'scratch_zero':['r6','r7'],
            'register_mapping':{'T':1,'W':2,'A':3,'D':4,'H':5,'S':6,'R':7,'L':8},
            'copy_D_to_S_tree':export(copy),
            'macro_old_sites':len(list(scan.leaf_occurrences(scan.env['node75']))),
            'contract':'(T,D,L,S,R)=(t,d,pair(x,tail),0,0) -> (4*pair(d+x,t),d+x,tail,0,0); all other registers unchanged',
            'finite_tests':tests,'largest_test_steps':largest,
            'occurrences':occurrences,'variants':records,
            'remaining':'Transposed implication requires a correct AX rho8 prefix, all constructor emissions, and a physical compiler plus PA proof transport.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('finite_tests','macro_old_sites','occurrences')}))
    print(json.dumps([{k:v for k,v in r.items() if k!='tree'} for r in records]))

if __name__=='__main__':main()
