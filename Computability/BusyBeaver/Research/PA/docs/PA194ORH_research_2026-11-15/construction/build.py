#!/usr/bin/env python3
"""Reassociate the closed operand routine while preserving its hidden history selector."""
import argparse,shutil
from pathlib import Path
import sys,json,hashlib
BASE=Path(__file__).resolve().parents[1]
PIN=Path(__file__).resolve().parent
INPUTS=PIN/'inputs'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=BASE/'machines/PA194ORH')
args=parser.parse_args()
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(PIN/'vendor'))
import compiler as c,support as s
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
orig=s.read_table(INPUTS/'primary.raw.native.tm')
oldnodes={k:tup(v)for k,v in json.loads((INPUTS/'AX11H.nodes.json').read_text()).items()}
g=c.read_grammar(INPUTS/'AX11H.grammar.json')
fixed={k:v for k,v in orig.items()if k[0]<1300};fixed[164,1]=(1,True,114)
for q,bit,a in json.loads((INPUTS/'h_shift_edits.json').read_text()):fixed[q,bit]=tuple(a)
c.machine=lambda:(fixed,[]);c.raw_nodes=lambda:oldnodes
INC=('leaf','inc',1)
c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
oldraw,oldindex,oldshape=c.build(g);oldsites,oldins,_=c.source(g)
oldfolds=json.loads((INPUTS/'primary.folds.json').read_text())
parent,_=s.apply_folds(oldraw,oldfolds)
pd,pl=s.dense_table(parent,194)
assert hashlib.sha256(s.table_text(pd).encode()).hexdigest()==json.loads((INPUTS/'parent.expected.json').read_text())['PA194AX11H']['dense_sha256']
nodes=dict(oldnodes)
assert nodes['node75']==('node74','node65')
assert nodes['node74']==('node32','node73') and nodes['node73']==('node53','node55')
nodes['node75']=('node32',('node53',('node55','node65')))
newfixed=dict(fixed)
newfixed.update({(69,0):(0,False,92),(92,0):(0,True,111),(92,1):(1,True,90),
 (213,0):(0,True,104),(213,1):(1,True,185),(185,0):(0,True,107),(185,1):(1,True,333),
 (333,0):(0,True,98),(333,1):(1,True,90)})
c.machine=lambda:(newfixed,[]);c.raw_nodes=lambda:nodes
c.MACROS[('node55','node65')]=333
raw,index,shape=c.build(g)
def renamed(q):
 if q not in oldshape:return q
 t=oldshape[q]
 return c.MACROS[t]if t in c.MACROS else index[t]
folds=[[renamed(a),renamed(b),[[w,d,renamed(q)]for w,d,q in acts]]for a,b,acts in oldfolds]
rows,aliases=s.apply_folds(raw,folds);local=s.check_local_folds(raw,rows,aliases,folds)
sites,ins,cs=c.source(g)
assert ins==oldins
runtime=c.validate(rows,cs);assert runtime['ok'],runtime
startup=s.startup(rows,sites[25][0])
dense,labels=s.dense_table(rows,194)
assert len(raw)==402 and len(shape)==66
for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw),('parent.tm',pd),('parent.native.tm',parent)]:
 (OUT/name).write_text(s.table_text(table))
for name,x in [('nodes.json',nodes),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_folds.json',local),('labels.json',labels)]:dump(name,x)
changed=sum(a[0]!=b[0] for a,b in zip(sites,oldsites))
receipt=dict(name='PA194ORH',states=194,rows=388,raw=201,fixed=135,readers=66,folds=7,
 source_sites=len(sites),source_outcomes=len(cs),source_instructions_identical=True,changed_source_addresses=changed,
 max_path_length=max(len(p)for p,_,_ in sites),runtime=runtime,startup=startup,
 sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
 parent_sha256=hashlib.sha256(s.table_text(pd).encode()).hexdigest(),
 local_selector_identity='old 69/0;213/0;92/0 equals new 69/0;92/0;111/0, and history-one old69/0;213/1 equals new69/0;92/1')
dump('receipt.json',receipt)
shutil.copy2(INPUTS/'AX11H.grammar.json',OUT/'grammar.json')
dump('parent.sites.json',[[''.join(map(str,p)),op,a]for p,op,a in oldsites])
dump('parent.instructions.json',oldins)
print(json.dumps(receipt,indent=2),flush=True)
