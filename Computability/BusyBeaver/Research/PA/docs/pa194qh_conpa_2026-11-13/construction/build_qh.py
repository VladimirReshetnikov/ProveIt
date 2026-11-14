#!/usr/bin/env python3
"""PA194QH: premise-exchanged quantifier distribution with visible-result no-push MP and cache-only Shift.

This reconstructs a new concrete synthesis of two credited prior mechanisms.
The universal certificates are executable evidence, not a Lean/Rocq endpoint.
"""
from pathlib import Path
import argparse, hashlib, json, sys
import compiler as c
import baseline_tools as b
HERE=Path(__file__).resolve().parent
BASE_NODES,BASE_MACHINE=c.raw_nodes,c.machine
FIXED_EDITS={(38,0):(0,True,11),(38,1):(1,True,122),
 (164,1):(1,True,114),(214,0):(0,True,312),
 (214,1):(1,True,20),(312,0):(0,True,188)}

def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def sha(x):return hashlib.sha256(x).hexdigest()
def nodes():
 ns=BASE_NODES()
 ns['node163']=('node6','node54')
 ns['node170']=(('node36',('node167','node145')),'node57')
 return ns

def fixed():
 rows,labels=BASE_MACHINE();rows.update(FIXED_EDITS);return rows,labels

def build(out,full=True):
 assert __debug__ and not sys.flags.optimize,'Run without Python -O'
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 c.raw_nodes,c.machine=nodes,fixed
 inc=('leaf','inc',1)
 c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 grammar=c.read_grammar(HERE/'inputs/q.grammar.json')
 oldgrammar=c.read_grammar(HERE/'inputs/primary.grammar.json')
 raw,idx,shape=c.build(grammar)
 folds=json.loads((HERE/'inputs/q.folds.json').read_text())
 child,aliases=b.apply_folds(raw,folds)
 local=b.check_local_folds(raw,child,aliases,folds)
 assert len(raw)==402 and len(shape)==67 and len(folds)==7
 assert len(child)==388 and len(local['cases'])==28
 original,_=BASE_MACHINE()
 assert all(child[q,bit]==original[q,bit]for q in c.BOXSTATES for bit in(0,1))
 sites,instructions,contracts=c.source(grammar)
 oldsites,oldinstructions,_=c.source(oldgrammar)
 assert len(sites)==len(oldsites)==3653
 assert json.loads(json.dumps(oldinstructions))==json.loads((HERE/'inputs/parent_H.instructions.json').read_text())
 changes=[i for i,(a,z)in enumerate(zip(instructions,oldinstructions))if a!=z]
 assert len(changes)==79 and min(changes)==1953 and max(changes)==2067
 runtime=c.validate(child,contracts)if full else None
 if full:assert runtime['ok'],runtime
 seed=b.startup(child,sites[25][0]);assert seed['steps']==57922
 dense,labels=b.dense_table(child,194)
 for n,r in[('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
  (out/n).write_text(b.table_text(r))
 for n,v in[('labels.json',labels),('nodes.json',nodes()),('folds.json',folds),
   ('local_cases.json',local),('instructions.json',instructions),
   ('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
   ('source.json',dict(sites=sites,instructions=instructions)),
   ('parent_H.instructions.json',oldinstructions),
   ('macro_word.json',b.word(b.expanded(grammar)))]:dump(out/n,v)
 receipt=dict(status='PASS',family='PA194QH',working_states=194,transition_rows=388,
  native_start=74,native_halt=254,dense_start=0,dense_halt=194,
  raw_states=201,fixed_states=134,AX_readers=67,folds=7,
  simultaneous_fold_cases=len(local['cases']),source_sites=len(sites),source_outcomes=len(contracts),
  changed_instruction_count_from_H=len(changes),changed_instruction_range_from_H=[min(changes),max(changes)],
  source_changes_from_H=changes,symbolic_runtime=runtime,startup=seed,
  generic_runtime_performed=full,arithmetic_box_rows_unchanged=True,
  dense_sha256=sha(b.table_text(dense).encode()),native_sha256=sha(b.table_text(child).encode()),
  fixed_edits_from_original_controller=[[q,bit,list(original[q,bit]),list(v)]for(q,bit),v in FIXED_EDITS.items()],
  kernel_checked=False,
  scope='Exact table/source construction, simultaneous folds, arbitrary-register physical contracts, complete blank initialization. PA calibration is an ordinary mathematical composition of the credited parent proofs.')
 dump(out/'construction_receipt.json',receipt)
 print(json.dumps({k:v for k,v in receipt.items()if k!='source_changes_from_H'},indent=2),flush=True)
 return receipt
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE.parent/'machine');ap.add_argument('--quick',action='store_true');a=ap.parse_args();build(a.output,not a.quick)
