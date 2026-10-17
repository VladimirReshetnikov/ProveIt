#!/usr/bin/env python3
"""Bounded associative rotations within closed source19 axiom subroutines."""
from __future__ import annotations
import argparse
from functools import cache
import importlib
import itertools
import json
from pathlib import Path
import random
import sys
import time
import rho8_grid as grid
g=grid.g


def canonical(nodes,names):
    # Preserve all non-grammar subroutines' definitions. Intern generated
    # closed pairs bottom-up and then discard unreachable generated pairs.
    generated={q for q,s in names.items() if s.startswith('axiom_grammar_')}
    out={q:es for q,es in nodes.items() if q not in generated}
    outnames={q:names[q] for q in out}
    intern={es:q for q,es in out.items()}
    fresh=max(nodes)+1
    @cache
    def make(q):
        nonlocal fresh
        if q not in generated:return q
        es=tuple(f'ENode {make(int(e[6:]))}' if e.startswith('ENode ') else e for e in nodes[q])
        if es not in intern:
            intern[es]=fresh;out[fresh]=es;outnames[fresh]=f'axiom_grammar_rotation_{fresh}';fresh+=1
        return intern[es]
    # Transform references from the unchanged outside program as well.
    for q in tuple(out):
        out[q]=tuple(f'ENode {make(int(e[6:]))}' if e.startswith('ENode ') else e for e in out[q])
    pending=[0];seen=set()
    while pending:
        q=pending.pop()
        if q in seen:continue
        seen.add(q)
        pending += [int(e[6:]) for e in out[q] if e.startswith('ENode ')]
    order=[0]+sorted(seen-{0});ids={q:i for i,q in enumerate(order)}
    return ({ids[q]:tuple(f'ENode {ids[int(e[6:])]}' if e.startswith('ENode ') else e for e in out[q]) for q in order},
            {ids[q]:outnames[q] for q in order})


def rotations(nodes,names):
    for q in nodes:
        if not names[q].startswith('axiom_grammar_'):continue
        a,c=nodes[q]
        if a.startswith('ENode '):
            b=int(a[6:])
            if names[b].startswith('axiom_grammar_'):
                d,e=nodes[b];fresh=max(nodes)+1
                nn=dict(nodes);nm=dict(names)
                nn[fresh]=(e,c);nm[fresh]='axiom_grammar_rotation_fresh'
                nn[q]=(d,f'ENode {fresh}')
                yield (q,'right'),canonical(nn,nm)
        if c.startswith('ENode '):
            b=int(c[6:])
            if names[b].startswith('axiom_grammar_'):
                d,e=nodes[b];fresh=max(nodes)+1
                nn=dict(nodes);nm=dict(names)
                nn[fresh]=(a,d);nm[fresh]='axiom_grammar_rotation_fresh'
                nn[q]=(f'ENode {fresh}',e)
                yield (q,'left'),canonical(nn,nm)


def fingerprint(nodes):
    @cache
    def key(q):
        return tuple(key(int(e[6:])) if e.startswith('ENode ') else e for e in nodes[q])
    # This expanded key distinguishes associations and is bounded at this DAG.
    return hash(key(0))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=100)
    p.add_argument('--seed',type=int,default=10616)
    a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    data=json.loads(a.source.read_text());orig={int(q):tuple(e) for q,e in data['nodes'].items()};on={int(q):s for q,s in data['names'].items()}
    nodes,names=canonical(orig,on);base=grid.measure(nodes)[0]
    best=(nodes,names);bestcost=base;current=(nodes,names);rng=random.Random(a.seed);trials=0;seen=set();history=[]
    start=time.monotonic()
    for step in range(a.rounds):
        moves=[]
        for move,(nn,nm) in rotations(*current):
            trials+=1
            cost,depth=grid.measure(nn)
            if cost>bestcost+1:continue
            fp=fingerprint(nn)
            if fp in seen:continue
            moves.append((cost,len(nn),depth,rng.random(),move,nn,nm,fp))
        if not moves:
            current=best;continue
        moves.sort(key=lambda x:x[:4])
        win=moves[0]
        if step%25==24:
            win=rng.choice(moves[:min(10,len(moves))])
        cost,_,depth,_,move,nn,nm,fp=win;seen.add(fp);current=(nn,nm)
        if cost<bestcost:
            best,bestcost=current,cost
            row=dict(step=step,trials=trials,cost=cost,decisions=len(nn),depth=depth,move=move)
            history.append(row);print(json.dumps(row),flush=True)
            grid.write_json(out/'best.dag.json',dict(root=0,nodes=nn,names=nm))
        if step%20==0:print(json.dumps(dict(step=step,trials=trials,current=cost,best=bestcost,seconds=time.monotonic()-start)),flush=True)
    nn,nm=best
    cert,stats=g.bisimulation(orig,nn)
    backendpath=grid.REPO/'lib/jeff-busy-beaver-zfc254/ZF/generator';sys.path.insert(0,str(backendpath));backend=importlib.import_module('TMBuilder')
    machine=g.compile_dag(backend,nn,nm);g.reextract(machine,nn,nm)
    named=out/'candidate.named.tm';machine.save(str(named))
    numeric,labels,meta=grid.normalize_named(named.read_bytes());(out/'candidate.tm').write_bytes(numeric)
    assert meta['working_states']==bestcost
    grid.write_json(out/'candidate.dag.json',dict(root=0,nodes=nn,names=nm))
    grid.write_json(out/'rm_certificate.json',cert);grid.write_json(out/'labels.json',labels)
    grid.write_json(out/'results.json',dict(initial=base,working_states=bestcost,trials=trials,rounds=a.rounds,seed=a.seed,
                    history=history,rm_certificate=stats,table=meta,seconds=time.monotonic()-start,
                    source=str(a.source),compiler_proof=False,ZFC_endpoint=False))
    print(json.dumps(dict(final=bestcost,trials=trials,rm=stats)),flush=True)


if __name__=='__main__':main()
