#!/usr/bin/env python3
"""Reconstruct PA194Q5/Q6 and verify exact source and physical certificates.

Python 3.10+ and the standard library suffice. Assertions must be enabled.
This is an executable certificate suite, not a proof-assistant endpoint.
"""
from pathlib import Path
import argparse, hashlib, json, sys
import compiler as c
import baseline_tools as b
import source_audit as audit

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
INC=('leaf','inc',1)
BASE_NODES=c.raw_nodes
EXPECTED={5:'150041f819135fa32b4521154823f1b96e635e8141329a6e8fbf15988baa073a',
          6:'7f53cacaa0533e601bad9685957a1ef5fede892533e0d62bd49684ef7cf984d4'}
EXPECTED_STEPS={5:1546445,6:1571284}

def sha(data):return hashlib.sha256(data).hexdigest()
def save(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')

def build(k,output):
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Do not run Python with -O; assertions are required.')
    c.raw_nodes=BASE_NODES
    base=b.read_table(HERE/'inputs/primary_raw201.native.tm')
    c.machine=lambda:(base,None)
    c.MACROS[(INC,INC)]=99
    c.MACROS[((INC,INC),(INC,INC))]=190
    grammar=c.read_grammar(HERE/'grammar.json')
    primary=c.read_grammar(HERE/'inputs/primary.grammar.json')
    oldsites,oldins,_=c.source(grammar)
    _,primaryins,_=c.source(primary)
    changed=[i for i,(u,v) in enumerate(zip(primaryins,oldins)) if u!=v]
    assert len(primaryins)==len(oldins)==3673
    assert len(changed)==79 and min(changed)==1953 and max(changed)==2067
    wold=b.word(b.expanded(primary));wnew=b.word(b.expanded(grammar))
    assert len(wold)==len(wnew)==190
    assert wold[:102]==wnew[:102] and wold[121:]==wnew[121:]

    raw,index,shape=c.build(grammar)
    assert len(shape)==67 and len(raw)==402
    raw.update({(190,0):(0,True,330),
                (190,1):(1,True,99 if k==5 else 330),
                (330,0):(0,True,61),(330,1):(1,True,99)})
    assert len(raw)==404
    folds=json.loads((HERE/'folds.json').read_text())
    extra=[41,99,[[0,False,30],[1,False,2040]]]
    opportunities=c.opportunities_fast(raw,{**shape,41:None,99:None})
    assert any(a==41 and z==99 and
               all(tuple(extra[2][bit]) in choices[bit] for bit in (0,1))
               for a,z,choices in opportunities)
    folds=folds+[extra]
    child,aliases=b.apply_folds(raw,folds)
    local=b.check_local_folds(raw,child,aliases,folds)
    assert len(folds)==8 and len(local['cases'])==32
    assert all(child[q,bit]==base[q,bit] for q in c.BOXSTATES for bit in (0,1))

    nodes=BASE_NODES();triple=(INC,'node60')
    nodes['node61']=(triple,'node60' if k==5 else triple)
    c.raw_nodes=lambda:nodes
    sites,instructions,contracts=c.source(grammar)
    binding=audit.source_binding(grammar,oldsites,oldins,nodes,sites,instructions,k)
    formulas=audit.emitter_audit(grammar,k)
    symbolic=c.validate(child,contracts)
    assert symbolic['ok'] and symbolic['contracts']==4780+61*(k-4)
    assert symbolic['total_steps']==EXPECTED_STEPS[k]
    assert symbolic['max_steps']==490
    seed=b.startup(child,sites[25][0])
    assert seed['steps']==58320
    dense,labels=b.dense_table(child,194)
    text=b.table_text(dense)
    assert sha(text.encode())==EXPECTED[k]
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    for filename,rows in [('machine.tm',dense),('machine.native.tm',child),('raw202.native.tm',raw)]:
        (output/filename).write_text(b.table_text(rows))
    for filename,obj in [('labels.json',labels),('nodes.json',nodes),('folds.json',folds),
                         ('local_fold_cases.json',local),('source_binding.json',binding),
                         ('emitter_audit.json',formulas),('instructions.json',instructions),
                         ('sites.json',[[list(p),op,a] for p,op,a in sites]),
                         ('macro_word.json',wnew),
                         ('q_change.json',{'changed_sites_at_radix4':changed,
                          'changed_macro_interval':[102,121],
                          'all_surrounding_macro_tokens_identical':True})]:
        save(output/filename,obj)
    receipt={'name':f'PA194Q{k}','status':'PASS','radix':k,'working_states':194,
             'transition_rows':388,'dense_start':0,'dense_halt':194,
             'native_start':74,'native_halt':254,'raw_states':202,
             'fixed_controls':135,'AX_readers':67,'simultaneous_folds':8,
             'local_fold_cases':32,'source_sites':len(sites),
             'source_outcomes':len(contracts),'source_max_depth':max(len(p) for p,_,_ in sites),
             'symbolic_runtime':symbolic,'startup':seed,'arithmetic_box_rows_unchanged':True,
             'dense_sha256':EXPECTED[k],'native_sha256':sha(b.table_text(child).encode()),
             'source_binding':{key:value for key,value in binding.items() if key!='bodies'},
             'emitter_audit':formulas,'controller':'original sum-Shift and original dummy-push MP',
             'kernel_checked':False,
             'proof_scope':'Exact construction, complete source binding, symbolic register contracts, '
              'simultaneous quotient checks and full blank startup. PA consistency calibration '
              'uses the separate ordinary mathematical argument and attributed inherited lemmas.'}
    save(output/'receipt.json',receipt)
    c.raw_nodes=BASE_NODES
    print(json.dumps({key:receipt[key] for key in ('name','status','working_states','source_sites',
          'source_outcomes','dense_sha256')},indent=2),flush=True)
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--radix',type=int,choices=[5,6],action='append')
    p.add_argument('--output',type=Path,default=PACKAGE/'machines')
    args=p.parse_args()
    for k in args.radix or [5,6]:build(k,args.output/f'PA194Q{k}')
