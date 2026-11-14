#!/usr/bin/env python3
"""Construct PA194AX11S and verify its exact physical/source certificates.

This new composition combines the supplied AX11 interface with the supplied
symmetric sum-test implementation. It does not close the baseline iPRA
calibration gap. Python 3.10+, standard library; run with assertions enabled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'construction'))
import compiler as c
import support as s

def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def gram_json(t):
    names, rules = {}, {}
    def go(t):
        if not c.isnode(t):
            return t
        if t in names:
            return names[t]
        name = 'g' + str(len(names))
        names[t] = name
        rules[name] = list(map(go, t))
        return name
    root = go(t)
    return {'root': root, 'rules': rules}

def source_binding(old, new):
    """Exact graph cut; the proof of the unbounded block is in the report."""
    assert len(old) == 3672 and len(new) == 3669
    k = len(new) - 2
    assert k == 3667 and old[:k] == new[:k]
    assert old[k:] == [('dec',6,k+3,k+1), ('inc',5,k+2),
                      ('jump',k), ('inc',6,k+4), ('jump',0)]
    assert new[k:] == [('inc',5,k+1), ('jump',0)]
    entry = k-7
    assert old[entry:k] == [('dec',1,entry+3,entry+1),
                           ('inc',6,entry+2), ('jump',entry),
                           ('dec',5,k,entry+4), ('inc',1,entry+5),
                           ('inc',6,entry+6), ('jump',entry+3)]
    assert old[:11] == [('dec',5,4,1),('dec',6,3,2),('jump',0),
                       ('jump',5),('dec',6,10,5),('dec',5,7,6),
                       ('jump',5),('dec',6,9,8),('jump',5),
                       ('jump',11),('halt',)]
    def edges(ins):
        return ins[2:] if ins[0] in ('inc','dec') else ins[1:] if ins[0]=='jump' else ()
    audits=[]
    for instructions in (old,new):
        external=[(i,j) for i,r in enumerate(instructions) for j in edges(r)
                  if i < entry and j >= entry]
        assert external == [(48,entry)], external
        incoming_cmp=[(i,j) for i,r in enumerate(instructions) for j in edges(r)
                      if i >= 11 and j < 11]
        assert incoming_cmp == [(len(instructions)-1,0)]
        audits.append({'external_shift_entry':external,'comparator_entry':incoming_cmp})
    return {'status':'PASS','old_sites':len(old),'new_sites':len(new),
            'unchanged_prefix':k,'shift_entry':entry,'old_trailer_length':5,
            'new_trailer_length':2,'graph_cut_audits':audits,
            'unbounded_equivalence':'proved separately by counter induction'}

def build(output, full=True):
    assert __debug__ and not sys.flags.optimize
    parent_dir = ROOT / 'reference/ax11'
    raw0 = s.read_table(parent_dir / 'raw.native.tm')
    oldnodes = {k:tup(v) for k,v in json.loads((parent_dir/'nodes.json').read_text()).items()}
    grammar = c.read_grammar(parent_dir/'grammar.json')
    c.machine = lambda:(raw0,[])
    c.raw_nodes = lambda:oldnodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    rebuilt,index,shape=c.build(grammar)
    assert rebuilt==raw0 and len(shape)==67
    oldsites,oldins,_=c.source(grammar)
    assert json.loads(json.dumps(oldins))==json.loads((parent_dir/'instructions.json').read_text())
    folds=json.loads((parent_dir/'folds.json').read_text())
    parent,pa=s.apply_folds(raw0,folds)
    assert parent==s.read_table(parent_dir/'machine.native.tm')
    raw=dict(raw0)
    assert raw[38,1]==(1,True,20) and raw[310,1]==(1,True,62)
    raw[38,1]=(1,True,30)
    raw[310,1]=(1,True,330)
    raw[330,0]=(0,True,63)
    raw[330,1]=(1,False,73)
    folds=folds+[[41,330,[[0,False,31],[1,False,46]]]]
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    assert len(raw)==404 and len(rows)==388 and len(local['cases'])==32
    ns=dict(oldnodes)
    assert ns['node168']==('node37','node57') and ns['node171']==('node170','node23')
    ns['node168']=('node37','node56')
    ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    c.raw_nodes=lambda:ns
    sites,instructions,contracts=c.source(grammar)
    binding=source_binding(oldins,instructions)
    assert len(contracts)==4775
    assert all(rows[q,b]==parent[q,b] for q in c.BOXSTATES for b in (0,1))
    validation=c.validate(rows,contracts) if full else None
    if full:
        assert validation['ok'],validation
    startup=s.startup(rows,sites[25][0])
    dense,labels=s.dense_table(rows,194)
    output.mkdir(parents=True,exist_ok=True)
    for filename,table in [('machine.native.tm',rows),('machine.tm',dense),('raw.native.tm',raw)]:
        (output/filename).write_text(s.table_text(table))
    values={'labels.json':labels,'nodes.json':ns,'grammar.json':gram_json(grammar),
            'grammar.tree.json':grammar,'sites.json':[[''.join(map(str,p)),op,a] for p,op,a in sites],
            'instructions.json':instructions,'folds.json':folds,'local_folds.json':local,
            'source_binding.json':binding}
    for filename,value in values.items():dump(output/filename,value)
    patch=[]
    for key in sorted(set(rows)|set(parent)):
        if rows.get(key)!=parent.get(key):
            patch.append({'state':key[0],'read':key[1],'old':parent.get(key),'new':rows.get(key)})
    dump(output/'native_changes.json',patch)
    receipt={'status':'PASS','family':'PA194AX11S','working_states':194,'transition_rows':388,
             'start':0,'halt':194,'native_start':74,'native_halt':254,
             'fixed_controls':135,'AX_readers':67,'folds':8,'local_fold_cases':32,
             'source_sites':len(sites),'source_contracts':len(contracts),'runtime':validation,
             'startup':startup,'source_binding':binding,'arithmetic_box_rows_unchanged':True,
             'dense_sha256':hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
             'native_sha256':hashlib.sha256(s.table_text(rows).encode()).hexdigest(),
             'kernel_checked':False,'ipra_consistency_equivalence_established':False,
             'claim':'New physical/source composition; inherits unproved baseline iPRA calibration.'}
    dump(output/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'machine')
    ap.add_argument('--quick',action='store_true',help='Skip construction symbolic replay; not full verification.')
    args=ap.parse_args()
    build(args.output,not args.quick)
