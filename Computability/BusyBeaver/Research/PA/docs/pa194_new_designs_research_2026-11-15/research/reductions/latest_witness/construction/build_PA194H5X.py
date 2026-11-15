#!/usr/bin/env python3
"""Reconstruct PA194H5X from frozen source grammar and nine local folds.

Python 3.10+, standard library. Run with assertions enabled. Source/arithmetic
calibration is a separate written proof; this checks literal construction,
source contracts, simultaneous folds, and exact complete blank startup.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import support as s
EXPECTED_DENSE='caffdd9f10d87d0d050eff07ab8f6e8edd9ab443aa94c948f03ee5316e37b614'
EXPECTED_NATIVE='f45696ad9e78599bcc469d887c6295a4dc4afa00ff90458e230c9ee3ad3966d3'

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x

def build(out,full=True):
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run with assertions enabled; do not use -O.')
 old=s.read_table(HERE/'inputs/raw.native.tm')
 ns={k:tup(v)for k,v in json.loads((HERE/'inputs/nodes.json').read_text()).items()}
 tree=tup(json.loads((HERE/'inputs/PA194H5X.grammar.tree.json').read_text()))
 folds=json.loads((HERE/'inputs/PA194H5X.folds.json').read_text())
 c.machine=lambda:(old,[]);c.raw_nodes=lambda:ns
 inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 raw,index,shape=c.build(tree)
 assert len(raw)==406 and len(shape)==69
 assert len(folds)==9 and sum(q<1300 for q,b in raw if b==0)==134
 rows,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,rows,aliases,folds)
 assert len(local['cases'])==36
 assert all(rows[q,b]==old[q,b]for q in c.BOXSTATES for b in(0,1))
 sites,instructions,contracts=c.source(tree)
 assert len(sites)==3677 and len(contracts)==4786
 validity=c.validate(rows,contracts)if full else None
 if full:assert validity['ok'] and validity['total_steps']==1546312,validity
 blank=s.startup(rows,sites[25][0]);assert blank['steps']==57922
 dense,labels=s.dense_table(rows,194)
 assert hashlib.sha256(s.table_text(dense).encode()).hexdigest()==EXPECTED_DENSE
 assert hashlib.sha256(s.table_text(rows).encode()).hexdigest()==EXPECTED_NATIVE
 out.mkdir(parents=True,exist_ok=True)
 for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:(out/name).write_text(s.table_text(table))
 receipt=dict(family='PA194H5X',status='PASS',working_states=194,rows=388,start=0,halt=194,raw_fixed=134,raw_readers=69,folds=9,local_fold_cases=36,source_sites=3677,source_outcomes=4786,formula_coefficient=4,AX_macro_tokens=189,source_emitter='h5X with independent consequent A, ordinary h6',source_store='G, N, H, AX11',source_contracts_replayed=full,runtime=validity,startup=blank,dense_sha256=EXPECTED_DENSE,native_sha256=EXPECTED_NATIVE,kernel_checked=False)
 for name,obj in [('receipt.json',receipt),('labels.json',labels),('nodes.json',ns),('grammar.tree.json',tree),('folds.json',folds),('fold_cases.json',local),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),('instructions.json',instructions)]:
  (out/name).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);p.add_argument('--quick',action='store_true',help='Skip construction-runtime contracts; record the omission explicitly.')
 a=p.parse_args();build(a.output.resolve(),not a.quick)
