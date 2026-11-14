#!/usr/bin/env python3
"""Combine PA194's AX decoder with the H-only Shift / cache-result MP controller.

This is a finite constructor and certificate verifier, not a Lean/Rocq proof.
The complete logical argument is in proof_notes.txt.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'construction'))
import compiler as c
import build194 as b

EDITS={(164,1):(1,True,130),(38,0):(0,True,11),(38,1):(1,True,122),
       (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}

def sha(data):return hashlib.sha256(data).hexdigest()

def main():
    if not __debug__:raise RuntimeError('Run without -O; assertions are part of the verifier.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--skip-symbolic',action='store_true')
    ap.add_argument('--output',type=Path,default=HERE/'output')
    args=ap.parse_args();out=args.output;out.mkdir(parents=True,exist_ok=True)
    grammar=c.read_grammar(HERE/'construction/source/pa194.grammar.json')
    folds=json.loads((HERE/'construction/source/pa194.folds.json').read_text())
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    old_machine,old_nodes=c.machine,c.raw_nodes
    old_sites,old_instructions,_=c.source(grammar)
    raw0,_,shape0=c.build(grammar)
    parent,_=b.apply_folds(raw0,folds)
    assert b.table_text(parent)==(HERE/'construction/tables/pa194.native.tm').read_text()
    def machine():
        table,labels=old_machine();table.update(EDITS);return table,labels
    def raw_nodes():
        nodes=old_nodes();nodes['node163']=('node6','node147')
        nodes['node170']=(('node36',('node167','node145')),'node57');return nodes
    c.machine,c.raw_nodes=machine,raw_nodes
    sites,instructions,contracts=c.source(grammar)
    assert len(sites)==3649 and len(contracts)==4749
    # Exact full graph comparison with the already calibrated Combined source.
    reference=HERE/'reference_195C.instructions.json'
    assert json.loads(json.dumps(instructions))==json.loads(reference.read_text())
    n=len(sites);E,F,S=n-15,n-12,n-11
    relocation={len(old_sites)-13:F,len(old_sites)-12:S}
    changed=[]
    for i in range(E):
        oi,ni=old_instructions[i],instructions[i]
        nargs=1 if oi[0]=='jump' else 2
        expected=oi[:nargs]+tuple(relocation.get(t,t)for t in oi[nargs:])
        assert expected==ni,(i,oi,ni)
        if oi!=ni:changed.append([i,list(oi),list(ni)])
    expected=[('dec',4,F,E+1),('inc',5,E+2),('jump',E),('jump',25),
              ('dec',1,S+2,S+1),('jump',S),('dec',5,S+6,S+3),
              ('inc',1,S+4),('inc',6,S+5),('jump',S+2),
              ('dec',6,S+9,S+7),('inc',5,S+8),('jump',S+6),
              ('inc',6,S+10),('jump',0)]
    assert instructions[E:]==expected
    assert [x[0]for x in changed]==[48,n-96,n-16]
    raw,_,shape=c.build(grammar)
    assert len(raw)==402 and len(shape)==67 and shape==shape0
    assert {key:raw[key] for key in raw if raw[key]!=raw0[key]}==EDITS
    child,aliases=b.apply_folds(raw,folds)
    local=b.check_local_folds(raw,child,aliases,folds)
    assert len(local['cases'])==28
    differences=[[q,bit,list(parent[q,bit]),list(act)]for(q,bit),act in sorted(child.items())if parent[q,bit]!=act]
    assert {tuple(x[:2])for x in differences}==set(EDITS)
    assert all(child[q,bit]==old_machine()[0][q,bit]for q in c.BOXSTATES for bit in(0,1))
    dense,labels=b.dense_table(child,194)
    native_text,dense_text=b.table_text(child),b.table_text(dense)
    (out/'pa194C.native.tm').write_text(native_text)
    (out/'pa194C.tm').write_text(dense_text)
    (out/'pa194C.labels.json').write_text(json.dumps(labels)+'\n')
    (out/'pa194C.sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a]for p,op,a in sites])+'\n')
    (out/'pa194C.instructions.json').write_text(json.dumps(instructions,indent=2)+'\n')
    (out/'local_folds.json').write_text(json.dumps(local,indent=2)+'\n')
    (out/'unfolded201C.native.tm').write_text(b.table_text(raw))
    startup=b.startup(child,sites[25][0]);assert startup['steps']==57922
    valid=None if args.skip_symbolic else c.validate(child,contracts)
    if valid is not None:assert valid['ok'],valid
    receipt=dict(family='PA194C',working_states=194,transitions=388,raw_states=201,
       raw_reader_states=67,folds=7,graph_reachable_working_states=len(labels)-1,
       native_start=74,native_halt=254,dense_start=0,dense_halt=194,
       source_sites=len(sites),source_contracts=len(contracts),
       source_instruction_graph_equal_to_195C=True,ax_grammar_unchanged=True,
       source_prefix_changes=changed,exact_command_tail=expected,
       native_row_changes=differences,local_fold_cases=len(local['cases']),
       symbolic_runtime=valid,startup=startup,
       native_sha256=sha(native_text.encode()),dense_sha256=sha(dense_text.encode()),
       proof_scope='Ordinary PA-provability argument plus executable certificates; no new end-to-end Lean proof')
    (out/'build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
