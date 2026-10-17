#!/usr/bin/env python3
"""Full-calculus cost census for nonuniform affine formula-constructor tags.

No formula parser is modified: this proof enumerator constructs implication
codes and compares them with its cache. Every original logical/theory macro,
proof enumeration rule, pair/list helper and nine-register order is retained.
This executable cost census is not a calibrated binary consistency machine.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

BASE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path[:0]=[str(BASE/'backend'),str(BASE/'reference')]
import TMBuilder as backend
import recover_wade_dag as recover

NODES,NAMES=recover.parse_dag((BASE/'reference/Dag254.v').read_text())
ROOTS=(119,181,180,182) # implication, membership, universal, equality
KINDS=('Imp','Rel','All','Eq')
DEFAULT=((4,0),(4,1),(4,2),(4,3))
INC='EInc 1'

@lru_cache(None)
def incs(n,register=1):
    assert n>=1
    inc=f'EInc {register}'
    return inc if n==1 else (incs(n-1,register),inc)

def make_dag(codecs):
    replacement=dict(zip(ROOTS,codecs))
    @lru_cache(None)
    def visit(q):
        if q in replacement:
            m,t=replacement[q]
            loop=('EDecnz 7',(incs(m),'EContinue 2'))
            base=(visit(160),(visit(162),loop))
            return base if t==0 else (base,incs(t))
        if q==177: # the only literal formula-1 writer is relative falsity
            return (visit(171),incs(codecs[1][1]))
        if q==152: # NIP compares the cache with the exact falsity code
            return (incs(codecs[1][1],6),visit(153))
        return tuple(visit(int(e.split()[1])) if e.startswith('ENode') else e for e in NODES[q])
    root=visit(0)
    ids={};new={};names={}
    def intern(t):
        if isinstance(t,str):return t
        if t not in ids:
            q=len(ids);ids[t]=q;names[q]='main().0' if q==0 else f'codec_node_{q:03}().0'
            new[q]=tuple(intern(v) for v in t)
        return f'ENode {ids[t]}'
    assert intern(root)=='ENode 0'
    return new,names

def cost_dag(nodes):
    @lru_cache(None)
    def zero(q):
        e=nodes[q][0]
        return 1+(zero(int(e.split()[1])) if e.startswith('ENode') else 0)
    z=max(map(zero,nodes))
    return len(nodes)+55+z,z

def actual_compile(nodes,names):
    machine=recover.compile_dag(backend,nodes,names)
    recover.reextract(machine,nodes,names)
    states={q for q,_ in machine.states}
    framework=sum(q[0].isdigit() for q in states)
    assert len(states)==cost_dag(nodes)[0]
    return machine,dict(decision=len(nodes),framework=framework,working=len(states),rows=len(machine.states))

def disjoint(p,q):
    m,a=p;n,b=q
    return (a-b)%math.gcd(m,n)!=0

def valid(c):
    return all(disjoint(a,b) for a,b in itertools.combinations(c,2))

def normalize(machine):
    states={q for q,_ in machine.states}
    order=[machine.start]+sorted(states-{machine.start})
    ids={q:i for i,q in enumerate(order)};ids['halt']=len(order)
    missing=[(q,b) for q in order for b in ('0','1') if (q,b) not in machine.states]
    assert missing==[('1.inc','1')]
    lines=['#! start 0']
    for q in order:
        for b in ('0','1'):
            a=machine.states.get((q,b))
            w,d,t=(b,'R','halt') if a is None else (a.write,a.direction,a.nextstate)
            lines.append(f'{ids[q]} {b} {w} {d} {ids[t]}')
    return '\n'.join(lines)+'\n'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-modulus',type=int,default=12)
    ap.add_argument('--output',type=Path,default=BASE/'affine_codec_results.json')
    args=ap.parse_args()
    started=time.monotonic();bound=args.max_modulus
    baseline,base_names=make_dag(DEFAULT)
    _,old=actual_compile(NODES,NAMES)
    _,rewritten=actual_compile(baseline,base_names)
    assert old==rewritten
    cases=[];best=old['working'];winners=[];depths={}
    oddtags=[(m,t) for m in range(2,bound+1) for t in range(1,m)]
    for mi in range(2,bound+1):
        imp=(mi,0)
        for mr in range(2,bound+1):
            rel=(mr,1)
            if not disjoint(imp,rel):continue
            available=[p for p in oddtags if disjoint(imp,p) and disjoint(rel,p)]
            for allc,eq in itertools.permutations(available,2):
                if not disjoint(allc,eq):continue
                c=(imp,rel,allc,eq)
                nodes,names=make_dag(c);cost,depth=cost_dag(nodes)
                entry=dict(codec=c,working=cost,decision=len(nodes),dispatcher_depth=depth)
                cases.append(entry)
                if depth not in depths:
                    _,counts=actual_compile(nodes,names);depths[depth]=counts
                if cost<best:best=cost;winners=[entry]
                elif cost==best:winners.append(entry)
    winner=min(cases,key=lambda x:(x['working'],sum(m+t for m,t in x['codec']),x['codec']))
    four_tag_permutations=[]
    for r,a,e in itertools.permutations((1,2,3)):
        c=((4,0),(4,r),(4,a),(4,e))
        nd,nm=make_dag(c);_,cnt=actual_compile(nd,nm)
        four_tag_permutations.append(dict(codec=c,**cnt))
    nodes,names=make_dag(tuple(map(tuple,winner['codec'])))
    machine,counts=actual_compile(nodes,names)
    table=normalize(machine)
    table_path=args.output.with_suffix('.tm');table_path.write_text(table)
    result=dict(title=__doc__,source_commit='43026ff42f0939f09b9e95495248cfadcad38e38',
       constructor_order=KINDS,max_modulus=bound,original=old,recompiled_uniform=rewritten,
       constraints=['Imp tag zero','Rel tag one','other tags strictly positive and below modulus',
        'pairwise disjoint infinite arithmetic progressions'],
       cases=len(cases),histogram=dict(Counter(c['working'] for c in cases)),best=best,winners=winners,
       depth_compiler_checks=depths,selected=winner,selected_actual=counts,
       four_tag_permutations=four_tag_permutations,
       selected_table_sha256=hashlib.sha256(table.encode()).hexdigest(),seconds=time.monotonic()-started,
       complete_source_logic_unchanged=True,lean_proof=False,zfc_machine_claim=False)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
