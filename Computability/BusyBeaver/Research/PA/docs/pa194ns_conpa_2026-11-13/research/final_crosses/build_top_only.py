#!/usr/bin/env python3
"""Rebuild a 195-state top-only-Shift experiment.

Requires --package pointing to the delivered PA194NS package. Uses its pinned
compiler and generic symbolic arithmetic-block contracts. This experiment has
construction-level physical evidence only: no independent literal audit,
complete new logical calibration, or consistency theorem is asserted.
"""
from pathlib import Path
import argparse,hashlib,json,sys
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--package',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
sys.path.insert(0,str(args.package/'construction'));import build as base
c=base.c
ns=base.BASE_NODES();ns['node163']=('node6','node54');ns['node168']=('node37',(('leaf','dec',5),'node38'));ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
c.raw_nodes=lambda:ns
EDITS={(164,1):(1,True,114),(38,1):(1,True,331),(331,0):(0,True,45),(331,1):(1,True,57),(310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73)}
def fixed():
 rows,labels=base.BASE_MACHINE();rows.update(EDITS);return rows,labels
c.machine=fixed
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
tree=c.read_grammar(args.package/'inputs/pa194.grammar.json');sites,code,contracts=c.source(tree);raw,_,shape=c.build(tree)
folds=json.loads((args.package/'inputs/pa194.folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
child,aliases=base.fold(raw,folds);local=base.local_checks(raw,child,aliases,folds)
states={q for q,b in child};assert len(states)==195 and len(child)==390 and len(raw)==406 and len(shape)==67
valid=c.validate(child,contracts);assert valid['ok']
assert len(sites)==3650 and len(contracts)==4750
# Complete seed check, independent of the PA194NS expected-duration constant.
expected={-3,46};path=sites[25][0];expected.update(-2+i for i,b in enumerate(path) if b)
physical=[0,0,0,0,0,0,2,0,0]+[1]*26;pos=47
for v in physical:pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
q,h,ones=74,0,set()
for step in range(58004):
 assert q!=254
 w,d,q=child[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1
assert(q,h,ones)==(84,-2,expected)
order=[74];index={74:0}
for q in order:
 for b in (0,1):
  t=child[q,b][2]
  if t!=254 and t not in index:index[t]=len(order);order.append(t)
assert set(order)==states;order.append(254)
dense={(index[q],b):(w,d,195 if t==254 else index[t]) for (q,b),(w,d,t) in child.items()}
args.output.mkdir(parents=True,exist_ok=True)
for name,rows in [('top195.native.tm',child),('top195.tm',dense),('raw203.native.tm',raw)]: (args.output/name).write_text(base.text_table(rows))
receipt={'status':'construction-level PASS only','working_states':195,'transition_rows':390,'raw_states':203,'AX_readers':67,'folds':8,'local_fold_cases':len(local),'source_sites':len(sites),'source_outcomes':len(contracts),'construction_symbolic_runtime':valid,'startup_steps':58004,'whole_seed_equal':True,'dense_sha256':hashlib.sha256(base.text_table(dense).encode()).hexdigest(),'native_sha256':hashlib.sha256(base.text_table(child).encode()).hexdigest(),'independent_literal_audit':False,'new_ConPA_theorem_claimed':False,'scope':'Higher-count experiment, not an accepted 194-state or sub194 consistency result.'}
for name,obj in [('receipt.json',receipt),('labels.json',order),('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),('instructions.json',code),('folds.json',folds),('local_cases.json',local)]: (args.output/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
