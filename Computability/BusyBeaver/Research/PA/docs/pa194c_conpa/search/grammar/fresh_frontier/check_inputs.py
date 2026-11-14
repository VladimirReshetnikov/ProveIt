#!/usr/bin/env python3
"""Bind the new search inputs to the literal packet and published source CFGs.

Pass the package construction directory as the only argument. This does not
validate reassociated search outputs and makes no claim of a state lower bound.
"""
from pathlib import Path
import hashlib,json,sys

P=Path(__file__).resolve().parent
construction=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(construction))
import build194 as b
import build194C as bc
c=b.c
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99
c.MACROS[((inc,inc),(inc,inc))]=190
t=c.read_grammar(P/'new194.grammar.json')
old=c.read_grammar(construction/'source/pa194.grammar.json')
assert b.word(b.expanded(t))==b.word(b.expanded(old))
assert len(b.word(b.expanded(t)))==190
folds=json.loads((P/'new194.folds.json').read_text())
receipts={}
for tag in ['S','C']:
    if tag=='C':bc.enable_combined()
    sites,instructions,contracts=c.source(t)
    baseline_sites,baseline_instructions,_=c.source(old)
    assert instructions==baseline_instructions
    assert [(op,a) for _,op,a in sites]==[(op,a) for _,op,a in baseline_sites]
    binding=(construction/'source/pa194.instructions.json' if tag=='S' else
             construction.parent/'verification/independent/reference_inputs/195C.instructions.json')
    assert json.loads(json.dumps(instructions))==json.loads(binding.read_text())
    raw,index,shape=c.build(t)
    assert len(shape)==68 and len(raw)==404
    packet_raw=b.read_table(P/'new194.unfolded202.native.tm')
    if tag=='C':packet_raw.update(bc.EDITS)
    assert raw==packet_raw
    lines=(P/f'start194alt{tag}.txt').read_text().splitlines()
    nb=int(lines[0]);actual={}
    for line in lines[1:1+nb]:
        q,w0,d0,n0,w1,d1,n1=map(int,line.split())
        actual[q,0]=(w0,bool(d0),n0);actual[q,1]=(w1,bool(d1),n1)
    assert actual=={k:v for k,v in raw.items() if k[0]<1300}
    child,aliases=b.apply_folds(raw,folds)
    local=b.check_local_folds(raw,child,aliases,folds)
    assert len(child)==388 and len(local['cases'])==32
    validation=c.validate(child,contracts)
    assert validation['ok'],validation
    startup=b.startup(child,sites[25][0])
    assert startup['steps']==(58154 if tag=='S' else 57922)
    dense,labels=b.dense_table(child,194)
    receipts[tag]={'raw_table_bound_to_new_packet':True,
                   'fixed_input_rows_bound_to_raw_table':True,
                   'macro_tokens':190,'macro_word_equal_to_old194':True,
                   'source_cfg_equal_to_published_reference':True,
                   'source_reference_sha256':hashlib.sha256(binding.read_bytes()).hexdigest(),
                   'source_sites':len(sites),'source_contracts':len(contracts),
                   'local_fold_cases':len(local['cases']),
                   'symbolic_validation':validation,
                   'startup_steps':startup['steps'],'whole_blank_tape_equal':True,
                   'native_sha256':hashlib.sha256(b.table_text(child).encode()).hexdigest(),
                   'dense_sha256':hashlib.sha256(b.table_text(dense).encode()).hexdigest(),
                   'dense_labeling':'Breadth first from native control 74; not the new packet sorted-state relabeling.'}
    print(tag,json.dumps(receipts[tag]),flush=True)
receipt={'status':'PASS','inputs':receipts,
         'scope':'Checks the starting inputs only. Universal symbolic source contracts use inherited arithmetic-block lemmas; no search result is certified here and no new kernel theorem is claimed.'}
(P/'input_validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
