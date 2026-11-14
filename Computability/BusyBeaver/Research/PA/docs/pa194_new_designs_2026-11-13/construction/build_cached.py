#!/usr/bin/env python3
"""Build PA194C: seven-fold separate-head decoder plus cached-head commands.

Frozen composition of two existing, independently checked optimizations.
This is executable mathematical evidence, not a new proof-assistant theorem.
"""
from pathlib import Path
import hashlib,json,sys
import compiler as c
import baseline_tools as b
ROOT=Path(__file__).resolve().parent
INP=ROOT/'inputs'
OUT=ROOT/'candidate'
START,HALT=74,254
if not __debug__:raise RuntimeError('Assertions are required; do not use -O.')

def sha(x):return hashlib.sha256(x).hexdigest()
def write_json(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def main():
    OUT.mkdir(exist_ok=True)
    original_machine,original_nodes=c.machine,c.raw_nodes
    original,labels=original_machine()
    dense_edits={(115,1):(1,True,108),(37,0):(0,True,11),(37,1):(1,True,101),
                 (127,0):(0,True,133),(127,1):(1,True,20),(133,0):(0,True,120)}
    edits={(labels[q],bit):(w,d,labels[n])for(q,bit),(w,d,n)in dense_edits.items()}
    def machine():
        rows,ls=original_machine();rows.update(edits);return rows,ls
    def nodes():
        ns=original_nodes();ns['node163']=('node6','node147')
        ns['node170']=(('node36',('node167','node145')),'node57');return ns
    c.machine,c.raw_nodes=machine,nodes
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(INP/'pa194.grammar.json')
    parent_grammar=c.read_grammar(INP/'195C.grammar.json')
    assert b.word(b.expanded(grammar))==b.word(b.expanded(parent_grammar))
    assert len(b.word(b.expanded(grammar)))==190
    sites,ins,contracts=c.source(grammar)
    ps,pi,pc=c.source(parent_grammar)
    assert ins==pi
    assert json.loads(json.dumps(ins))==json.loads((INP/'195C.instructions.json').read_text())
    assert len(sites)==3649 and len(contracts)==4749
    raw,index,shape=c.build(grammar)
    parent_raw,_,parent_shape=c.build(parent_grammar)
    assert len(raw)==402 and len(shape)==67 and len(parent_shape)==67
    folds=json.loads((INP/'pa194.folds.json').read_text())
    parent_folds=json.loads((INP/'195C.folds.json').read_text())
    assert len(folds)==7 and len(parent_folds)==6
    child,aliases=b.apply_folds(raw,folds)
    parent,pa=b.apply_folds(parent_raw,parent_folds)
    assert parent==b.read_table(INP/'195C.machine.native.tm')
    local=b.check_local_folds(raw,child,aliases,folds)
    b.check_local_folds(parent_raw,parent,pa,parent_folds)
    old194=b.read_table(INP/'pa194.native.tm')
    changes={key:(old194[key],child[key])for key in old194 if old194[key]!=child[key]}
    assert set(changes)==set(edits)
    assert all(child[key]==act for key,act in edits.items())
    assert all(child[q,bit]==original[q,bit]for q in c.BOXSTATES for bit in (0,1))
    print('Built 194C; 3,649 source sites and 4,749 contracts; validating.',flush=True)
    valid=c.validate(child,contracts);assert valid['ok'],valid
    pvalid=c.validate(parent,pc);assert pvalid['ok'],pvalid
    startup=b.startup(child,sites[25][0]);assert startup['steps']==57922
    parent_startup=b.startup(parent,ps[25][0]);assert parent_startup['steps']==57922
    dense,ls=b.dense_table(child,194)
    native=b.table_text(child).encode();dense_bytes=b.table_text(dense).encode()
    (OUT/'pa194C.native.tm').write_bytes(native)
    (OUT/'pa194C.tm').write_bytes(dense_bytes)
    write_json(OUT/'pa194C.labels.json',ls)
    write_json(OUT/'pa194C.instructions.json',ins)
    write_json(OUT/'pa194C.sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites])
    write_json(OUT/'pa194C.local_cases.json',local)
    (OUT/'pa201C.native.tm').write_text(b.table_text(raw))
    receipt={'family':'PA194C','working_states':194,'transition_rows':388,'start':0,'halt':194,
      'native_start':74,'native_halt':254,'fixed_states':134,'raw_reader_states':67,'folds':7,
      'source_sites':len(sites),'source_outcomes':len(contracts),'macro_tokens':190,
      'source_graph_identical_to_pinned_195C':True,'pinned_195C_rebuilt_exactly':True,
      'local_folds_cases':len(local['cases']),'maximum_fold_duration':max(x['duration']for x in local['cases']),
      'symbolic_validation':valid,'parent_symbolic_validation':pvalid,'startup':startup,
      'parent_startup':parent_startup,
      'native_sha256':sha(native),'dense_sha256':sha(dense_bytes),
      'controller_changes':[[q,bit,list(old),list(new)]for(q,bit),(old,new)in sorted(changes.items())],
      'kernel_checked':False}
    write_json(OUT/'construction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
