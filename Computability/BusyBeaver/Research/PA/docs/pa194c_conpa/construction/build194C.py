#!/usr/bin/env python3
"""Compose the PA194 AX reader with the published 195C cached-head controller.

All six physical edits and both source replacements are copied from
PA195_ConPA_research_2026-11-14.zip:construction195/build_check.py.
This checks a new composition; it does not claim a newly kernel-checked theorem.
"""
from pathlib import Path
import json, hashlib, sys
import build194 as b
c=b.c
HERE=Path(__file__).resolve().parent
OUT=HERE/'rebuilt_194C'
EDITS={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,130),
       (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
PARENT_C_SHA='8f34d9e5cc2e64ecc49bbc8581dc29b2ac0a84ad9187c4dd8b7597588ef22ea3'

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

def enable_combined():
    old_machine,old_nodes=c.machine,c.raw_nodes
    def machine():
        rows,labels=old_machine();rows.update(EDITS);return rows,labels
    def nodes():
        ns=old_nodes()
        ns['node163']=('node6','node147')
        ns['node170']=(('node36',('node167','node145')),'node57')
        return ns
    c.machine,c.raw_nodes=machine,nodes

def main():
    assert __debug__ and not sys.flags.optimize
    OUT.mkdir(exist_ok=True)
    # Bind the untouched source and parent before applying the six edits.
    b.build(full=False)
    enable_combined()
    grammar=c.read_grammar(HERE/'source/pa194.grammar.json')
    pg=c.read_grammar(HERE/'inputs/parent195S.grammar.json')
    assert b.word(b.expanded(grammar))==b.word(b.expanded(pg))
    assert len(b.word(b.expanded(grammar)))==190
    sites,instructions,contracts=c.source(grammar)
    ps,pi,pc=c.source(pg)
    assert instructions==pi and [(op,a) for p,op,a in sites]==[(op,a) for p,op,a in ps]
    assert len(sites)==3649 and len(contracts)==4749
    published_path=HERE.parent/'verification/independent/reference_inputs/195C.instructions.json'
    published_bytes=published_path.read_bytes()
    assert hashlib.sha256(published_bytes).hexdigest()=='0afee1346c0931b3b91fea70571b01fd665a802ab9327409e4030f673412f5e3'
    assert json.loads(json.dumps(instructions))==json.loads(published_bytes)
    raw,idx,shapes=c.build(grammar)
    pr,_,pshapes=c.build(pg)
    assert len(shapes)==len(pshapes)==67 and len(raw)==len(pr)==402
    folds=json.loads((HERE/'source/pa194.folds.json').read_text())
    pf=json.loads((HERE/'inputs/parent195S.folds.json').read_text())
    child,aliases=b.apply_folds(raw,folds)
    parent,pa=b.apply_folds(pr,pf)
    # Literal table hash independently binds the source modifications to 195C.
    assert sha(b.table_text(parent))==PARENT_C_SHA
    local=b.check_local_folds(raw,child,aliases,folds)
    b.check_local_folds(pr,parent,pa,pf)
    assert len(local['cases'])==28
    assert len(child)==388
    baseline,_=b.ORIGINAL_MACHINE()
    assert all(child[q,bit]==baseline[q,bit] for q in c.BOXSTATES for bit in (0,1))
    valid=c.validate(child,contracts)
    parent_valid=c.validate(parent,pc)
    assert valid['ok'] and parent_valid['ok']
    blank=b.startup(child,sites[25][0]);parent_blank=b.startup(parent,ps[25][0])
    assert blank['steps']==parent_blank['steps']==57922
    dense,labels=b.dense_table(child,194)
    native_text,dense_text=b.table_text(child),b.table_text(dense)
    (OUT/'pa194C.native.tm').write_text(native_text)
    (OUT/'pa194C.tm').write_text(dense_text)
    (OUT/'pa194C.labels.json').write_text(json.dumps(labels)+'\n')
    (OUT/'pa194C.instructions.json').write_text(json.dumps(instructions,indent=2)+'\n')
    (OUT/'pa194C.sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a] for p,op,a in sites])+'\n')
    (OUT/'parent195C.native.tm').write_text(b.table_text(parent))
    (OUT/'parent195C.instructions.json').write_text(json.dumps(pi,indent=2)+'\n')
    (OUT/'local_fold_certificate.json').write_text(json.dumps(local,indent=2)+'\n')
    (OUT/'startup.json').write_text(json.dumps(blank,indent=2)+'\n')
    changed=[list(k)+list(v) for k,v in sorted(child.items()) if v!=b.read_table(HERE/'tables/pa194.native.tm')[k]]
    assert len(changed)==6
    receipt={'family':'PA194C','working_states':194,'transition_rows':388,'raw_states':201,
      'fixed_controls':134,'raw_readers':67,'folds':7,'source_sites':len(sites),
      'source_contracts':len(contracts),'source_word_equal_to_195C':True,
      'resolved_source_map_equal_to_195C':True,'parent195C_native_sha256':PARENT_C_SHA,
      'published_195C_source_map_equal':True,
      'published_195C_source_map_sha256':hashlib.sha256(published_bytes).hexdigest(),
      'native_sha256':sha(native_text),'dense_sha256':sha(dense_text),
      'symbolic_validation':valid,'parent_symbolic_validation':parent_valid,
      'startup_steps':blank['steps'],'whole_tape_startup':True,
      'local_fold_cases':len(local['cases']),'changed_native_rows_from_PA194':changed,
      'ordinary_mathematical_transfer_target':'PA proves Nonhalt(PA194C) iff Con(PA)',
      'new_kernel_checked_endpoint':False}
    (OUT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
