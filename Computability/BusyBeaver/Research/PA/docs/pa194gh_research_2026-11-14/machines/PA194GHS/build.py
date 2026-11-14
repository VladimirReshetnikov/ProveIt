#!/usr/bin/env python3
from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent;src=HERE.parent/'PA194GH';out=HERE
sys.path.insert(0,str(src/'construction'))
import compiler as c
import support as s

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
raw=s.read_table(src/'raw.native.tm')
raw.update({(214,1):(1,True,30),(310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73)})
nodes={k:tup(v)for k,v in json.loads((src/'nodes.json').read_text()).items()}
nodes['node170']=(('node36',('node167','node145')),'node56')
nodes['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
c.machine=lambda:(raw,[]);c.raw_nodes=lambda:nodes
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
grammar=c.read_grammar(src/'grammar.json')
r,_,shape=c.build(grammar);assert r==raw
folds=json.loads((src/'folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
child,aliases=s.apply_folds(raw,folds);cases=s.check_local_folds(raw,child,aliases,folds)
sites,ins,cs=c.source(grammar);print('source',len(sites),len(cs),flush=True)
run=c.validate(child,cs);assert run['ok'];print(run,flush=True)
blank=s.startup(child,sites[25][0]);print('blank',blank['steps'],flush=True)
dense,labels=s.dense_table(child,194)
for name,rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
 assert (out/name).read_text()==s.table_text(rows),name
receipt=dict(name='PA194GHS',working_states=194,transitions=388,raw_fixed_states=135,raw_reader_states=len(shape),folds=len(folds),source_sites=len(sites),source_outcomes=len(cs),runtime=run,startup=blank,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),kernel_checked=False,ipra_calibration_complete=False)
for name,x in [('receipt.json',receipt),('labels.json',labels),('nodes.json',nodes),('grammar.json',json.loads((src/'grammar.json').read_text())),('folds.json',folds),('fold_cases.json',cases),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),('instructions.json',ins)]:
 if name=='receipt.json':(out/name).write_text(json.dumps(x,indent=2)+'\n')
 else:assert json.loads((out/name).read_text())==json.loads(json.dumps(x)),name
print(json.dumps(receipt,indent=2))
