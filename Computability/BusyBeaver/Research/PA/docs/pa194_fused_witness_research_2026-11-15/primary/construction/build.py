#!/usr/bin/env python3
"""Deterministically reconstruct PA194FW from the frozen grammar and folds.

The inherited compiler/runtime utility code remains in vendor/ with attribution.
All source/controller changes and every fold are locally checked here. The
independent verifier imports none of these construction modules.
"""
from pathlib import Path
import sys,json,itertools,argparse,hashlib,shutil
BASE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(BASE/'construction/vendor'))
import compiler as c
import support as s

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x

def build(grammar,out,full=True):
 old=s.read_table(BASE/'construction/inputs/raw.native.tm')
 nodes={k:tup(v)for k,v in json.loads((BASE/'construction/inputs/nodes.json').read_text()).items()}
 assert nodes['node170']==(('node36',('node167','node145')),'node57')
 changed=dict(old);changed.update({(214,1):(1,True,30),(310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73)})
 nodes['node170']=(('node36',('node167','node145')),'node56')
 nodes['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
 c.machine=lambda:(changed,[]);c.raw_nodes=lambda:nodes
 inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
 tree=c.read_grammar(grammar)
 raw,index,shape=c.build(tree)
 fixedfold=[[41,330,[[0,False,31],[1,False,46]]]]
 stage,aliases0=s.apply_folds(raw,fixedfold);local0=s.check_local_folds(raw,stage,aliases0,fixedfold)
 folds=json.loads((BASE/'construction/inputs/folds.json').read_text())
 rows,aliases=s.apply_folds(stage,folds)
 local=s.check_local_folds(stage,rows,aliases,folds)
 controls=len(rows)//2
 print('STATES',controls,'READERS',len(shape),'FOLDS',len(folds)+1,flush=True)
 assert controls==194
 sites,ins,contracts=c.source(tree)
 if full:
  runtime=c.validate(rows,contracts);print('RUNTIME',runtime,flush=True);assert runtime['ok']
 else:runtime=None
 startup=s.startup(rows,sites[25][0]);print('STARTUP',startup['steps'],flush=True)
 dense,labels=s.dense_table(rows,controls)
 assert all(rows[q,b]==old[q,b]for q in c.BOXSTATES for b in (0,1))
 out.mkdir(parents=True,exist_ok=True)
 for n,r in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw),('fixedfold.native.tm',stage)]:
  (out/n).write_text(s.table_text(r))
 for n,r in [('labels.json',labels),('nodes.json',nodes),('grammar.tree.json',tree),('fixedfold.json',fixedfold),('folds.json',folds),('fixedfold_cases.json',local0),('fold_cases.json',local),('sites.json',[[''.join(map(str,p)),o,a]for p,o,a in sites]),('instructions.json',ins)]:
  (out/n).write_text(json.dumps(r,indent=2)+'\n')
 shutil.copy2(grammar,out/'grammar.json')
 rec=dict(name='PA194FW',working_states=controls,raw_fixed_states=135,reader_states=len(shape),fixed_folds=1,reader_folds=len(folds),source_sites=len(sites),source_contracts=len(contracts),runtime=runtime,startup=startup,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),native_sha256=hashlib.sha256(s.table_text(rows).encode()).hexdigest(),source_change='Fuse the old h4 and existential-equality witness h5 into N(I(h4,U(D,N(E(H,D)))))',kernel_checked=False)
 (out/'construction_receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps(rec),flush=True)
 return rec
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=BASE/'rebuild'/'PA194FW');p.add_argument('--quick',action='store_true',help='omit redundant construction-side symbolic replay; independent replay remains available');a=p.parse_args();build(BASE/'construction/inputs/grammar.json',a.out,not a.quick)
