#!/usr/bin/env python3
"""Rebuild PA194QHS and check exact source and contextual-fold bindings.

The QH emitter/controller and symmetric cached-Shift mechanism are credited
in NOTICE.txt. This constructs their new literal composition. Python checks
are executable mathematical evidence, not a proof-assistant kernel theorem.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import compiler as c
import helpers as h
HERE=Path(__file__).resolve().parent
BASE_NODES,BASE_MACHINE=c.raw_nodes,c.machine
FIXED_EDITS={(38,0):(0,True,11),(38,1):(1,True,122),
 (164,1):(1,True,114),(214,0):(0,True,312),
 (214,1):(1,True,20),(312,0):(0,True,188)}
EXPECTED='3bf22abe66e327d63d1feacacda9cc6f1b6529d09ca779c10f22fa5ed3acd103'

def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def sha(data):return hashlib.sha256(data).hexdigest()
def qh_nodes():
 ns=BASE_NODES();ns['node163']=('node6','node54')
 ns['node170']=(('node36',('node167','node145')),'node57')
 return ns

def qhs_nodes():
 ns=qh_nodes();ns['node170']=(('node36',('node167','node145')),'node56')
 ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
 return ns

def fixed():
 rows,labels=BASE_MACHINE();rows.update(FIXED_EDITS);return rows,labels

def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else()

def build(out,full=True):
 assert __debug__ and not sys.flags.optimize,'Run without Python -O'
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 c.machine=fixed;c.raw_nodes=qh_nodes
 inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 grammar=c.read_grammar(HERE/'inputs/q.grammar.json')
 parent_raw,idx,shape=c.build(grammar)
 parent_folds=json.loads((HERE/'inputs/q.folds.json').read_text())
 parent,parent_alias=h.apply_folds(parent_raw,parent_folds)
 assert parent==h.read_table(HERE/'inputs/parent_QH.machine.native.tm')
 h.check_local_folds(parent_raw,parent,parent_alias,parent_folds)
 oldsites,oldins,_=c.source(grammar)
 assert json.loads(json.dumps(oldins))==json.loads((HERE/'inputs/parent_QH.instructions.json').read_text())
 parent_seed=h.startup(parent,oldsites[25][0]);assert parent_seed['steps']==57922
 c.raw_nodes=qhs_nodes
 raw=dict(parent_raw)
 raw.update({(214,1):(1,True,30),(310,1):(1,True,330),
             (330,0):(0,True,63),(330,1):(1,False,73)})
 folds=parent_folds+[[41,330,[[0,False,31],[1,False,46]]]]
 child,aliases=h.apply_folds(raw,folds)
 local=h.check_local_folds(raw,child,aliases,folds)
 assert len(raw)==404 and len(shape)==67 and len(folds)==8
 assert len(child)==388 and len(local['cases'])==32
 original,_=BASE_MACHINE()
 assert all(child[q,b]==original[q,b]for q in c.BOXSTATES for b in(0,1))
 sites,ins,contracts=c.source(grammar)
 assert len(oldins)==3653 and len(ins)==3650 and len(contracts)==4750
 assert ins[:3648]==oldins[:3648]
 assert oldins[3648:]==[('dec',6,3651,3649),('inc',5,3650),('jump',3648),('inc',6,3652),('jump',0)]
 assert ins[3648:]==[('inc',5,3649),('jump',0)]
 incoming=[(i,t)for i,row in enumerate(oldins[:3648])for t in targets(row)if t>=3648]
 assert all(t==3648 for i,t in incoming)and incoming
 # The incoming block empties H into T and scratch X; its last decrement exits here.
 assert incoming==[(3644,3648)]
 assert oldins[3644:3648]==[('dec',5,3648,3645),('inc',1,3646),('inc',6,3647),('jump',3644)]
 binding=dict(parent_sites=3653,child_sites=3650,unchanged_prefix_length=3648,
   parent_suffix=oldins[3648:],child_suffix=ins[3648:],only_external_suffix_entries=incoming,
   predecessor_block=oldins[3644:3648],parent_native_sha256=sha(h.table_text(parent).encode()),
   parent_instruction_sha256=sha((HERE/'inputs/parent_QH.instructions.json').read_bytes()),
   scope='Exact whole-source splice. Universal loop/comparison preservation is proved in proof/shift_preservation.tex.')
 runtime=c.validate(child,contracts)if full else None
 if full:assert runtime['ok'],runtime
 seed=h.startup(child,sites[25][0]);assert seed['steps']==57768
 dense,labels=h.dense_table(child,194)
 assert sha(h.table_text(dense).encode())==EXPECTED
 for name,table in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
  (out/name).write_text(h.table_text(table))
 for name,data in [('labels.json',labels),('nodes.json',qhs_nodes()),('folds.json',folds),
   ('local_cases.json',local),('instructions.json',ins),
   ('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
   ('source.json',dict(sites=sites,instructions=ins)),('source_binding.json',binding)]:dump(out/name,data)
 receipt=dict(status='PASS',family='PA194QHS',working_states=194,transition_rows=388,
  native_start=74,native_halt=254,dense_start=0,dense_halt=194,raw_states=202,
  fixed_states=135,AX_readers=67,folds=8,simultaneous_fold_cases=len(local['cases']),
  source_sites=len(sites),source_outcomes=len(contracts),symbolic_runtime=runtime,startup=seed,
  parent_startup_steps=parent_seed['steps'],generic_runtime_performed=full,
  arithmetic_box_rows_unchanged=True,dense_sha256=EXPECTED,
  native_sha256=sha(h.table_text(child).encode()),kernel_checked=False,
  scope='Exact source splice, simultaneous folds, universal primitive contracts, and complete blank initialization. PA calibration is a separate mathematical composition.')
 dump(out/'construction_receipt.json',receipt)
 print(json.dumps({k:v for k,v in receipt.items()if k!='startup'},indent=2),flush=True)
 return receipt
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE.parent/'generated_machine');ap.add_argument('--quick',action='store_true');args=ap.parse_args();build(args.output,not args.quick)
