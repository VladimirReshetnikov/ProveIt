#!/usr/bin/env python3
"""Reconstruct AX11GH/AX11GHS from frozen attributed GH/GHS source inputs.

Python 3.10+, standard library.  No repository, network, or search is needed.
The independent literal checker re-proves the arithmetic block certificates.
This constructor alone is not a proof-assistant kernel or a PA calibration.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import support as s

def tup(x):
    return tuple(map(tup,x)) if isinstance(x,list) else x

def replace_final_jump(tree):
    if tree==c.BREAK:return 'node49'
    return tuple(map(replace_final_jump,tree)) if c.isnode(tree) else tree

def build(family,output,full=True):
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run with assertions enabled; do not use -O or PYTHONOPTIMIZE.')
    assert family in ('PA194AX11GH','PA194AX11GHS')
    parent=HERE/'inputs'/family.replace('AX11','')
    expected=json.loads((ROOT/'expected.json').read_text())[family]
    raw_parent=s.read_table(parent/'raw.native.tm')
    nodes={k:tup(v)for k,v in json.loads((parent/'nodes.json').read_text()).items()}
    c.machine=lambda:(raw_parent,[])
    c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    old=c.read_grammar(parent/'grammar.json')
    tree=replace_final_jump(old)
    raw,index,shape=c.build(tree)
    folds=json.loads((parent/'folds.json').read_text())
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    sites,instructions,contracts=c.source(tree)
    assert len(sites)==expected['source_sites']
    assert len(contracts)==expected['source_outcomes']
    assert len(folds)==expected['folds']
    assert len(shape)==expected['raw_readers']
    assert sum(q<1300 for q,b in raw if b==0)==expected['raw_fixed']
    assert all(rows[q,b]==raw_parent[q,b]for q in c.BOXSTATES for b in(0,1))
    validity=c.validate(rows,contracts) if full else None
    if full:assert validity['ok'],validity
    blank=s.startup(rows,sites[25][0])
    assert blank['steps']==expected['startup_steps']
    dense,labels=s.dense_table(rows,194)
    assert hashlib.sha256(s.table_text(dense).encode()).hexdigest()==expected['dense_sha256']
    assert hashlib.sha256(s.table_text(rows).encode()).hexdigest()==expected['native_sha256']
    output.mkdir(parents=True,exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (output/name).write_text(s.table_text(table))
    receipt=dict(family=family,status='PASS',**expected,construction_contracts_replayed=full,
                 runtime=validity,startup=blank,local_fold_cases=len(local['cases']),
                 kernel_checked=False,
                 scope='Exact source, local folds, symbolic source contracts and complete blank initialization; calibration is a separate written proof.')
    for name,obj in [('receipt.json',receipt),('labels.json',labels),('nodes.json',nodes),
                     ('grammar.tree.json',tree),('folds.json',folds),('fold_cases.json',local),
                     ('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),
                     ('instructions.json',instructions)]:
        (output/name).write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family',choices=('PA194AX11GH','PA194AX11GHS'),required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--quick',action='store_true',help='Skip construction contracts; explicitly recorded.')
    a=p.parse_args();build(a.family,a.output.resolve(),not a.quick)
