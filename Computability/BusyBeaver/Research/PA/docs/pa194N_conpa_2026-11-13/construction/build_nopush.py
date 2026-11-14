#!/usr/bin/env python3
"""Rebuild PA194N, the separate-head no-push modus-ponens machine.

All dependencies are local and Python standard-library only. This is an
executable source/tape certificate, not a newly checked Lean/Rocq theorem.
"""
from pathlib import Path
import hashlib,json
import compiler as c
import baseline_tools as b
HERE=Path(__file__).resolve().parent
INPUT=HERE/'inputs'
OUT=HERE/'machine'
if not __debug__:raise RuntimeError('Run with assertions enabled.')

def sha(data):return hashlib.sha256(data).hexdigest()
def write_json(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def graph_targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else[]

def build():
    original_nodes,original_machine=c.raw_nodes,c.machine
    original,_=original_machine()
    def nodes():
        ns=original_nodes()
        assert ns['node163']==('node6','node55')
        assert ns['node55']==('node49','node54')
        ns['node163']=('node6','node54')
        return ns
    def machine():
        rows,labels=original_machine()
        assert rows[164,1]==(1,True,98)
        rows[164,1]=(1,True,114)
        return rows,labels
    c.raw_nodes,c.machine=nodes,machine
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99
    c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(INPUT/'pa194.grammar.json')
    raw,index,shape=c.build(grammar)
    folds=json.loads((INPUT/'pa194.folds.json').read_text())
    child,aliases=b.apply_folds(raw,folds)
    cases=b.check_local_folds(raw,child,aliases,folds)
    parent=b.read_table(INPUT/'pa194.native.tm')
    changes={key:(parent[key],child[key])for key in child if parent[key]!=child[key]}
    assert changes=={(164,1):((1,True,98),(1,True,114))}
    assert len(shape)==67 and len(raw)==402 and len(child)==388
    assert all(child[q,bit]==original[q,bit]for q in c.BOXSTATES for bit in(0,1))
    sites,instructions,contracts=c.source(grammar)
    old=json.loads((INPUT/'pa194.instructions.json').read_text())
    ins=json.loads(json.dumps(instructions))
    assert len(old)==3673 and len(ins)==3654 and len(contracts)==4755
    lo,hi=3634,3653
    def relocate(i):
        assert not lo<i<hi
        return i if i<=lo else i-(hi-lo)
    outside=0
    incoming=[]
    for pc,row in enumerate(old):
        if lo<=pc<hi:continue
        prefix=2 if row[0]in('inc','dec')else 1
        for dest in graph_targets(row):
            if lo<=dest<hi:incoming.append([pc,dest])
        translated=row[:prefix]+[relocate(x)for x in row[prefix:]]
        assert ins[relocate(pc)]==translated,(pc,translated,ins[relocate(pc)])
        outside+=1
    assert incoming==[[3628,3634]]
    expected=[['dec',4,4,1],['inc',1,2],['inc',6,3],['jump',0],
              ['dec',6,7,5],['inc',4,6],['jump',4]]
    normalized=[]
    for row in ins[lo:lo+7]:
        k=2 if row[0]in('inc','dec')else 1
        normalized.append(row[:k]+[x-lo for x in row[k:]])
    assert normalized==expected
    runtime=c.validate(child,contracts)
    assert runtime['ok']
    seed=b.startup(child,sites[25][0]);assert seed['steps']==58154
    dense,labels=b.dense_table(child,194)
    OUT.mkdir(exist_ok=True)
    native_bytes=b.table_text(child).encode()
    dense_bytes=b.table_text(dense).encode()
    assert sha(native_bytes)=='b38dfe8cbd6e84aadbea5912e20f25b0bbda8f3fad4fbec0c779a77c857a8dc8'
    assert sha(dense_bytes)=='37f7e909724cab7fd667db28f89b9c81653d2576c033750e783b40b3289c04f9'
    (OUT/'pa194N.native.tm').write_bytes(native_bytes)
    (OUT/'pa194N.tm').write_bytes(dense_bytes)
    write_json(OUT/'labels.json',labels)
    write_json(OUT/'sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites])
    write_json(OUT/'instructions.json',instructions)
    write_json(OUT/'fold_cases.json',cases)
    receipt={'name':'PA194N','working_states':194,'transition_rows':388,
      'native_start':74,'native_halt':254,'dense_start':0,'dense_halt':194,
      'fixed_controls':134,'raw_reader_controls':67,'simultaneous_folds':7,
      'source_sites':3654,'source_outcomes':4755,'old_source_sites':3673,
      'removed_old_interval_half_open':[lo,hi],'remaining_instructions_relocated_exactly':outside,
      'external_entries_into_removed_block':incoming,'retained_copy_loop':expected,
      'native_edit':{'state':164,'read':1,'old':[1,'R',98],'new':[1,'R',114]},
      'symbolic_runtime':runtime,'startup':seed,
      'native_sha256':sha(native_bytes),'dense_sha256':sha(dense_bytes),
      'kernel_checked':False,
      'scope':'Exact source splice, all primitive tape contracts, simultaneous folds and complete blank startup. Command calibration is a separate ordinary proof.'}
    write_json(OUT/'construction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2))
    return receipt
if __name__=='__main__':build()
