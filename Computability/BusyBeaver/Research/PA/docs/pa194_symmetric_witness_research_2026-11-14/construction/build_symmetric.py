#!/usr/bin/env python3
"""Rebuild the symmetric H5X and JH5X physical machines from pinned inputs.

The only new transformation is the symmetric cache test, independently
checked at source, local-fold, literal-tape, and full-startup levels.
The imported inputs/compiler are attributed in WITNESS_PROVENANCE.json.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor'))
import compiler as c
import support as s

EXPECTED = {
    'PA194H5XS': 'e4941ef9961b7184f18d01162889a45742be97da271ca9692a17c833628d8640',
    'PA194JH5XS': 'a10f76ac7bf8d3d473a3eaad82756353ae9ba7118225a12de52f10c80c625474',
}

def tup(x):
    return tuple(map(tup,x)) if isinstance(x,list) else x

def build(name, output, full=True):
    assert __debug__ and not sys.flags.optimize
    assert name in ('PA194H5XS', 'PA194JH5XS')
    parent=name[:-1]
    old=s.read_table(HERE/'inputs/raw.native.tm')
    nodes={k:tup(v) for k,v in json.loads((HERE/'inputs/nodes.json').read_text()).items()}
    tree=tup(json.loads((HERE/'inputs'/f'{parent}.grammar.tree.json').read_text()))
    folds=json.loads((HERE/'inputs'/f'{parent}.folds.json').read_text())
    assert nodes['node170']==(('node36',('node167','node145')),'node57')
    assert nodes['node171']==('node170','node23')
    assert old[214,1] == (1,True,20)
    assert old[310,1] == (1,True,62)
    edits={(214,1):(1,True,30),(310,1):(1,True,330),
           (330,0):(0,True,63),(330,1):(1,False,73)}
    changed=dict(old);changed.update(edits)
    nodes['node170']=(('node36',('node167','node145')),'node56')
    nodes['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    folds += [[41,330,[[0,False,31],[1,False,46]]]]
    c.machine=lambda:(changed,[])
    c.raw_nodes=lambda:nodes
    c.PHYSICAL[:]=[6,2,0,4,3,7,8,5,1]
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    raw,index,shape=c.build(tree)
    assert len(raw)==408 and len(shape)==69 and len(folds)==10
    rows,aliases=s.apply_folds(raw,folds)
    cases=s.check_local_folds(raw,rows,aliases,folds)
    assert len(cases['cases'])==40
    assert all(rows[q,b]==old[q,b] for q in c.BOXSTATES for b in (0,1))
    sites,instructions,contracts=c.source(tree)
    expected=(3674,4782) if parent=='PA194H5X' else (3680,4790)
    assert (len(sites),len(contracts))==expected
    runtime=c.validate(rows,contracts) if full else None
    if full:assert runtime['ok'],runtime
    startup=s.startup(rows,sites[25][0])
    assert startup['steps']==57768
    dense,labels=s.dense_table(rows,194)
    assert hashlib.sha256(s.table_text(dense).encode()).hexdigest()==EXPECTED[name]
    output.mkdir(parents=True,exist_ok=True)
    for filename,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (output/filename).write_text(s.table_text(table))
    payload={'labels.json':labels,'nodes.json':nodes,'grammar.tree.json':tree,
             'folds.json':folds,'fold_cases.json':cases,
             'sites.json':[[''.join(map(str,p)),op,arg] for p,op,arg in sites],
             'instructions.json':instructions}
    for filename,value in payload.items():
        (output/filename).write_text(json.dumps(value,indent=2)+'\n')
    digest=lambda f:hashlib.sha256((output/f).read_bytes()).hexdigest()
    receipt=dict(name=name,parent=parent,status='PASS',working_states=194,
                 transitions=388,raw_fixed_states=135,raw_reader_states=69,
                 simultaneous_folds=10,local_fold_cases=40,
                 source_sites=len(sites),source_outcomes=len(contracts),
                 runtime=runtime,full_construction_validation=full,startup=startup,
                 physical_edits={f'{q},{b}':a for (q,b),a in edits.items()},
                 dense_sha256=digest('machine.tm'),native_sha256=digest('machine.native.tm'),
                 source_change='Duplicate cache into T,X; leave H zero; increment H; compare 1 with old cache',
                 kernel_checked=False)
    (output/'construction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--machine',choices=('PA194H5XS','PA194JH5XS'))
    p.add_argument('--quick',action='store_true')
    a=p.parse_args()
    for name in ([a.machine] if a.machine else ['PA194H5XS','PA194JH5XS']):
        build(name,a.output/name,not a.quick)
