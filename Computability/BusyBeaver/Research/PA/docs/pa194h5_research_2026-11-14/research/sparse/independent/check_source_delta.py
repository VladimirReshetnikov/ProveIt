#!/usr/bin/env python3
"""Independently check the single extra fresh-candidate increment in even195HX.

Both baseline and child graphs are resolved in two independent ways from
their source paths. No compiler or builder is imported.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import source_language as source

def resolve(sites):
    ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,ops[o],a]for p,o,a in sites]
    graph,_=source.graph_arithmetic(mapped)
    assert graph==source.graph_intervals(mapped)
    names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    return [[names[e[0]]]+e[1:]+targets for e,targets in graph]

def check(inputs,output):
    assert __debug__ and not sys.flags.optimize
    old=resolve(json.loads((inputs/'primary.sites.json').read_text()))
    new=resolve(json.loads((inputs/'source.sites.json').read_text()))
    assert old==json.loads((inputs/'primary.instructions.json').read_text())
    assert new==json.loads((inputs/'source.instructions.json').read_text())
    assert len(old)==3673 and len(new)==3674
    assert old[27]==['dec',0,31,28]
    assert old[31]==['inc',0,32] and old[33]==['jump',31]
    assert new[31]==['inc',0,32]
    relocation=lambda i:i if i<31 else i+1
    for i,row in enumerate(old):
        split=2 if row[0]in('inc','dec')else 1
        expected=row[:split]+[relocation(t)for t in row[split:]]
        if i==27:
            assert expected==['dec',0,32,28]
            expected=['dec',0,31,28]
        assert new[relocation(i)]==expected,(i,row,new[relocation(i)])
    incoming=[]
    for i,row in enumerate(new):
        split=2 if row[0]in('inc','dec')else 1
        for branch,t in enumerate(row[split:]):
            if t==31:incoming.append([i,branch])
    assert incoming==[[27,0]]
    assert new[34]==['jump',32]
    receipt={
        'status':'PASS','baseline_sites':3673,'child_sites':3674,
        'all_3673_old_sites_preserved':True,
        'relocation':'i when i<31; i+1 otherwise',
        'inserted_site':31,'inserted_instruction':['inc',0,32],
        'sole_redirected_old_edge':{'source':27,'branch':'decrement zero','old_target':31,'relocated_target':32,'actual_target':31},
        'all_other_successor_edges_exactly_relocated':True,
        'only_incoming_edge_to_added_increment':incoming,
        'restoration_back_edge':['jump',32],
        'restoration_loop_skips_added_increment':True,
        'both_graphs_resolved_arithmetically_and_by_intervals':True,
        'input_sha256':{n:hashlib.sha256((inputs/n).read_bytes()).hexdigest()for n in ['primary.sites.json','primary.instructions.json','source.sites.json','source.instructions.json']},
        'scope':'Exact finite CFG relation. Together with the inherited fresh-candidate loop meaning, the extra increment occurs once on entry and is skipped by the restoration loop.'
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs',type=Path,default=HERE/'inputs')
    p.add_argument('--output',type=Path,default=HERE/'recorded/source_delta.json')
    a=p.parse_args();check(a.inputs,a.output)
