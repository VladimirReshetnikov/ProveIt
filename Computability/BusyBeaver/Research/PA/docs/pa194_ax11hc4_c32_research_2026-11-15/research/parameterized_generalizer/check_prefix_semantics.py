#!/usr/bin/env python3
"""Exact insertion/CFG check and symbolic macro identity for the new AX field."""
from pathlib import Path
import json,sys
import compiler as c,support as s
P=Path(__file__).resolve().parent

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
nodes={k:tup(v) for k,v in json.loads((P/'primary.nodes.json').read_text()).items()}
c.raw_nodes=lambda:nodes
c.machine=lambda:(s.read_table(P/'primary.raw.native.tm'),[])
def expand(x):
 if isinstance(x,str):return expand(nodes[x])
 if len(x)==3:return [x]
 return expand(x[0])+expand(x[1])
def flat(t):return flat(t[0])+flat(t[1]) if c.isnode(t) else [t]
orig=c.read_grammar(P/'primary.grammar.json')
new=c.read_grammar(P/'newgen_189.grammar.json')
a,old,_=c.source(orig)
b,newins,_=c.source(new)
assert nodes['node75']==('node74','node65')
assert nodes['node74']==('node32','node73')
assert nodes['node73']==('node53','node55')
# Identify the one insertion from the operation/register stream.
opsold=[(op,arg) for p,op,arg in a]
opsnew=[(op,arg) for p,op,arg in b]
inserted=[(x[1],x[2]) for x in expand('node32')+expand('node53')]
assert len(inserted)==14
poss=[i for i in range(len(opsold)+1) if opsnew==opsold[:i]+inserted+opsold[i:]]
assert len(poss)==1
start=poss[0];end=start+len(inserted)
def relocate(i):return i+14 if i>=start else i
def targets(ins):return ins[2:] if ins[0] in ('inc','dec') else ins[1:] if ins[0]=='jump' else ()
def rel(ins):
 prefix=ins[:2] if ins[0] in ('inc','dec') else ins[:1]
 return tuple(prefix)+tuple(relocate(i) for i in targets(ins))
diffs=[]
for i,ins in enumerate(old):
 j=relocate(i)
 if tuple(newins[j])!=rel(ins):diffs.append((i,j,list(rel(ins)),newins[j]))
assert len(diffs)==1
assert [start if x==end else x for x in diffs[0][2]]==list(diffs[0][3]), (start,end,diffs)
# No edge from outside enters the interior, and inserted segment has one exit.
entered=[];exits=set()
for i,ins in enumerate(newins):
 for j in targets(ins):
  if not start<=i<end and start<=j<end:entered.append((i,j))
  if start<=i<end and not start<=j<end:exits.add(j)
assert all(j==start for i,j in entered) and exits=={end}
# Evaluate the two distinct macro words over a free constructor algebra.
# These are the inherited total arithmetic macro equations; they are not
# asserted as new independent physical block proofs.
def plus(x,y):return ('add',x,y)
def push(x,w):return ('pair',x,w)
def cons(x,y):return ('I',x,y)
def execute(word,st):
 t,w,d,h,tmp,L=st
 for token in word:
  if token=='node58':w,t=push(t,w),h
  elif token=='node55':w,t=push(t,w),d
  elif token=='node65':
   assert w[0]=='pair'
   t,w=cons(w[1],t),w[2]
  elif token=='node75':
   # Source identity node75=(node32,(node53,node55)),node65
   assert L[0]=='pair'
   tmp,L=L[1],L[2]      # node32 unpairs continuation
   d,tmp=plus(d,tmp),0   # node53 transfers its head into d
   w,t=push(t,w),d       # node55 preserves t and copies d
   t,w=cons(w[1],t),w[2] # node65 constructs and pops
  else:
   assert token==('leaf','inc',1)
   t=plus(t,1)
 return t,w,d,h,tmp,L
state=('t','w','d','h',0,('pair','a','Ltail'))
newprefix=execute(flat(new)[:4],state)
oldprefix_after_offset=execute(flat(orig)[:5],
    ('t','w',plus('d','a'),'h',0,'Ltail'))
assert newprefix==oldprefix_after_offset
receipt=dict(old_sites=len(old),new_sites=len(newins),inserted_sites=14,insertion_interval=[start,end],old_other_source_instructions_and_targets_equal=True,changed_common_edges=diffs,outside_entries=entered,inserted_exit=end,macro_identity="new AX(c,a,x,y)(t,w,d,h) = old AX(c,x,y)(t,w,d+a,h)",identity_scope="exact block decomposition + inherited unpair/move/copy/cons arithmetic contracts; no new independent arithmetic engine proof")
(P/'parameterized_generalizer'/'source_prefix_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
