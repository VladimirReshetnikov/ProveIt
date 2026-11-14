#!/usr/bin/env python3
"""Replay the existing 203-control HS/radix-six composition and its checks.

This is construction verification, not a fresh reduction search. No network,
checkout or proof assistant is required. Run with assertions enabled.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import compiler as c
import support as s
ROOT=Path(__file__).resolve().parent
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def sha(text):return hashlib.sha256(text.encode()).hexdigest()
def verify():
    assert __debug__ and not sys.flags.optimize
    parent=s.read_table(ROOT/'raw202.native.tm')
    raw=dict(parent)
    edits={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,114),
           (214,0):(0,True,312),(214,1):(1,True,30),(312,0):(0,True,188),
           (310,1):(1,True,331),(331,0):(0,True,63),(331,1):(1,False,73)}
    raw.update(edits)
    ns={k:tup(v)for k,v in json.loads((ROOT/'parent6.nodes.json').read_text()).items()}
    ns['node163']=('node6','node54')
    ns['node170']=(('node36',('node167','node145')),'node56')
    ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    c.raw_nodes=lambda:ns
    sites,ins,contracts=c.source(c.read_grammar(ROOT/'grammar.json'))
    folds=json.loads((ROOT/'parent6.folds.json').read_text())
    child,aliases=s.apply_folds(raw,folds)
    assert len(raw)==406 and len(child)==390
    assert len(sites)==3772 and len(contracts)==4872
    local=s.check_local_folds(raw,child,aliases,folds)
    assert len(folds)==8 and len(local['cases'])==32
    assert all(child[q,b]==parent[q,b]for q in c.BOXSTATES for b in (0,1))
    assert child==s.read_table(ROOT/'recorded/machine195.native.tm')
    assert json.loads(json.dumps(ins))==json.loads((ROOT/'recorded/instructions.json').read_text())
    assert json.loads(json.dumps(ns))==json.loads((ROOT/'recorded/nodes.json').read_text())

    # This is replay of the original finite one-history-bit opportunity census.
    incoming={}
    for (q,b),(w,d,t)in raw.items():incoming.setdefault(t,set()).add((w,d))
    shape={q for q,b in raw if incoming.get(q)in ({(0,True)},{(1,True)})}
    ops=c.opportunities_fast(raw,shape)
    ops=[op for op in ops if incoming[op[0]]=={(0,True)} and incoming[op[1]]=={(1,True)}]
    assert json.loads(json.dumps(ops))==json.loads((ROOT/'recorded/opportunities.json').read_text())
    assert len(ops)==9 and len(c.max_matching(ops))==8
    assert {(a,b)for a,b,_ in ops if a==41}=={(41,99),(41,331)}
    runtime=c.validate(child,contracts)
    assert runtime=={'ok':True,'contracts':4872,'max_steps':508,'total_steps':1566770}
    startup=s.startup(child,sites[25][0]);assert startup['steps']==57760
    dense,labels=s.dense_table(child,195)
    return {
      'status':'Existing failed sub-194 composition, physically verified at195 states.',
      'pinned_commit':'317b07268681b44ff352d173a162e2a8c241b2fe',
      'raw_working_controls':203,'selected_simultaneous_folds':8,
      'folded_working_controls':195,'transition_rows':390,
      'raw_fixed_controls':136,'raw_AXIOM_readers':67,
      'conflicting_extra_folds':[[41,99],[41,331]],
      'conflict_explanation':'Both proposed identifications remove native control41, so their state savings cannot both be counted.',
      'one_history_bit_opportunities':9,'maximum_matching_in_this_census':8,
      'source_sites':3772,'source_outcomes':4872,'local_fold_cases':32,
      'symbolic_runtime':runtime,'whole_tape_startup':startup,
      'native_start':74,'native_halt':254,'dense_start':0,'dense_halt':195,
      'native_sha256':sha(s.table_text(child)),
      'raw_sha256':sha(s.table_text(raw)),
      'dense_sha256':sha(s.table_text(dense)),
      'proof_scope':'Finite construction and universal symbolic source simulation using inherited arithmetic-block summaries whose literal rows are unchanged. No new independent block-derivation replay, no end-to-end Lean/Rocq theorem, and no state-count lower bound.',
      'source_binding':'Complete supplied source nodes, resolved instruction graph, exact retained native table, and all source outcomes checked.',
      'dense_labels':labels}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    result=verify()
    text=json.dumps(result,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')
