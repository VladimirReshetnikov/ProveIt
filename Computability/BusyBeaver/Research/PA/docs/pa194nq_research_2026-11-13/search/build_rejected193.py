"""Rejected 193-state coefficient-three machine: physical validity only.

The associated numerical calculus is inconsistent. This is not a Con(PA)
machine. Its source is retained to expose a tempting invalid reduction.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT/'construction'
sys.path.insert(0,str(BASE))
import compiler as c,symbolic_runtime as s,baseline_tools as b
c.ROOT=s.ROOT=BASE/'reference'
original_nodes,original_machine=c.raw_nodes,c.machine
INC=('leaf','inc',1)
c.MACROS[(INC,INC)]=99
c.MACROS[((INC,INC),(INC,INC))]=190
grammar=c.read_grammar(BASE/'inputs/pa194.grammar.json')
raw,_,shape=c.build(grammar)
raw[190,0]=(0,True,61)
raw[190,1]=(1,True,99)
nodes=original_nodes()
nodes['node61']=(INC,'node60')
c.raw_nodes=lambda:nodes
folds=json.loads((BASE/'inputs/pa194.folds.json').read_text())
folds += [[41,99,[[0,False,30],[1,False,2035]]]]
child,aliases=b.apply_folds(raw,folds)
local=b.check_local_folds(raw,child,aliases,folds)
print('states',len(child)//2,'local cases',len(local['cases']),flush=True)
sites,instructions,contracts=c.source(grammar)
valid=c.validate(child,contracts)
print('source validation',valid,flush=True)
assert valid['ok']
seed=b.startup(child,sites[25][0])
print('startup',seed['steps'],flush=True)
dense,labels=b.dense_table(child,193)
out=ROOT/'search/rejected193'
out.mkdir(exist_ok=True)
for name,table in [('machine.native.tm',child),('machine.tm',dense)]:
 (out/name).write_text(b.table_text(table))
for name,data in [('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',instructions),('labels.json',labels),('folds.json',folds),('local_folds.json',local)]:
 (out/name).write_text(json.dumps(data,indent=2)+'\n')
receipt={'status':'REJECTED: coefficient-three calculus derives contradiction',
 'states':193,'source_sites':len(sites),'contracts':len(contracts),
 'symbolic_validation':valid,'seed':seed,
 'sha256':hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest()}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='seed'},indent=2))
