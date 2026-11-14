#!/usr/bin/env python3
"""Build two top-result/no-push, cache-test PA194 hybrid controllers.

The arithmetic and AX source are inherited. New work combines the no-push
MP with cache-only Shift and proves the resulting command interface.
"""
from pathlib import Path
import argparse, hashlib, json
import compiler as c
import baseline_tools as b

HERE=Path(__file__).resolve().parent
BASE_NODES,BASE_MACHINE=c.raw_nodes,c.machine
EXPECTED={'H':'3276a34fd0388102dad87a8b12c70e88b2bcccf6b068cb034ce78d33536adcc1',
          'HS':'19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1'}
def sha(data):return hashlib.sha256(data).hexdigest()
def js(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')

def build(family,out):
    assert __debug__
    c.raw_nodes,c.machine=BASE_NODES,BASE_MACHINE
    original,labels=BASE_MACHINE()
    # Five old cached-Shift edits; omit the cached-MP success edit.
    dense_edits={(37,0):(0,True,11),(37,1):(1,True,101),
                 (127,0):(0,True,133),(127,1):(1,True,20),(133,0):(0,True,120)}
    edits={(labels[q],bit):(w,d,labels[n])for(q,bit),(w,d,n)in dense_edits.items()}
    edits[164,1]=(1,True,114)
    def machine():
        rows,ls=BASE_MACHINE();rows.update(edits);return rows,ls
    ns=BASE_NODES()
    assert ns['node163']==('node6','node55')
    ns['node163']=('node6','node54')
    ns['node170']=(('node36',('node167','node145')),'node57')
    if family=='HS':
        ns['node170']=(('node36',('node167','node145')),'node56')
        ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    c.machine=machine;c.raw_nodes=lambda:ns
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(HERE/'inputs/pa194.grammar.json')
    raw,_,shape=c.build(grammar)
    folds=json.loads((HERE/'inputs/pa194.folds.json').read_text())
    if family=='HS':
        raw.update({(214,1):(1,True,30),(310,1):(1,True,330),
                    (330,0):(0,True,63),(330,1):(1,False,73)})
        folds=folds+[[41,330,[[0,False,31],[1,False,46]]]]
    child,aliases=b.apply_folds(raw,folds)
    cases=b.check_local_folds(raw,child,aliases,folds)
    assert len(child)==388
    assert all(child[q,bit]==original[q,bit]for q in c.BOXSTATES for bit in(0,1))
    sites,ins,contracts=c.source(grammar)
    runtime=c.validate(child,contracts);assert runtime['ok'],runtime
    seed=b.startup(child,sites[25][0])
    dense,ls=b.dense_table(child,194)
    out.mkdir(parents=True,exist_ok=True)
    for name,rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
        (out/name).write_text(b.table_text(rows))
    assert sha((out/'machine.tm').read_bytes())==EXPECTED[family]
    for name,data in [('labels.json',ls),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
                      ('instructions.json',ins),('source.json',dict(sites=sites,instructions=ins)),
                      ('nodes.json',ns),('folds.json',folds),('fold_cases.json',cases)]:js(out/name,data)
    old=b.read_table(HERE/'inputs/pa194.native.tm')
    receipt={'family':'PA194'+family,'working_states':194,'transition_rows':388,
      'native_start':74,'native_halt':254,'dense_start':0,'dense_halt':194,
      'fixed_controls_before_folds':len(raw)//2-len(shape),'AX_readers':len(shape),'folds':len(folds),
      'source_sites':len(sites),'source_outcomes':len(contracts),
      'symbolic_runtime':runtime,'startup':seed,
      'dense_sha256':sha((out/'machine.tm').read_bytes()),
      'native_sha256':sha((out/'machine.native.tm').read_bytes()),
      'changed_rows_from_primary':[[q,bit,old.get((q,bit)),act]for(q,bit),act in child.items()if old.get((q,bit))!=act],
      'kernel_checked':False,
      'scope':'All source outcomes, simultaneous local folds, dense conjugacy and full blank seed; new command compiler is a separate mathematical proof.'}
    js(out/'construction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--family',choices=['H','HS'],default='HS')
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    build(args.family,args.output or HERE.parent/'machines'/('PA194'+args.family))
