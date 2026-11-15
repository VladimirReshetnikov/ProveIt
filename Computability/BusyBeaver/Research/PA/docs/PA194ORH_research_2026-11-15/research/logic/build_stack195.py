#!/usr/bin/env python3
"""Rebuild and check the 195-state direct stack-result experiment.

This is an auxiliary experiment, not the delivered 194-state result.
It uses the retained construction checker, whose scope and provenance
are described in README.txt and reference/PROVENANCE.upstream.json.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
REF=HERE/'reference'
sys.path.insert(0,str(REF/'construction'))
import compiler as c
import support as s

def tup(x):
    return tuple(map(tup,x)) if isinstance(x,list) else x

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'replay_stack195')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    raw0=s.read_table(REF/'unfolded201.native.tm')
    nodes={k:tup(v) for k,v in json.loads((REF/'inputs/primary.nodes.json').read_text()).items()}
    nodes['mp_result_push']=('node54','node49')
    nodes['node163']=('node6','mp_result_push')
    raw0[164,1]=(1,True,330)
    raw0[330,0]=(0,True,114)
    raw0[330,1]=(1,True,19)
    c.machine=lambda:(raw0,[])
    c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(REF/'inputs/primary.grammar.json')
    raw,index,shape=c.build(grammar)
    folds=json.loads((REF/'inputs/primary.folds.json').read_text())
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    sites,ins,contracts=c.source(grammar)
    runtime=c.validate(rows,contracts)
    assert runtime['ok']
    startup=s.startup(rows,sites[25][0])
    dense,labels=s.dense_table(rows,195)
    native=s.table_text(rows)
    assert native==(HERE/'stack_result195.native.tm').read_text()
    assert s.table_text(raw)==(HERE/'stack_result202.raw.tm').read_text()
    (args.output/'machine.tm').write_text(s.table_text(dense))
    (args.output/'machine.native.tm').write_text(native)
    for name,value in [('labels.json',labels),('sites.json',sites),('instructions.json',ins),
                       ('folds.json',folds),('local_folds.json',local)]:
        (args.output/name).write_text(json.dumps(value,indent=2)+'\n')
    receipt={'working_states':len(rows)//2,'rows':len(rows),'raw_states':len(raw)//2,
        'source_sites':len(sites),'contracts':len(contracts),'folds':len(folds),
        'runtime':runtime,'startup':startup,
        'native_sha256':hashlib.sha256(native.encode()).hexdigest(),
        'dense_sha256':hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
        'scope':'195-state auxiliary direct stack-result machine; source and physical contracts checked, not a sub194 result or a Lean proof.'}
    (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
