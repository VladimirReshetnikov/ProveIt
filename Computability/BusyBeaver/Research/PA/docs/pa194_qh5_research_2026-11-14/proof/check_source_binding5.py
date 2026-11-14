#!/usr/bin/env python3
"""Exact source relocation from QH6 to QH5, including all successor targets.

The changed loop is 61 occurrences of six increments -> five increments.
All other primitive operations and successor targets are preserved. This
does not assert literal equality of trajectories for different encodings.
"""
from pathlib import Path
import argparse, hashlib, json, sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
INPUT=ROOT/'construction/inputs'
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns6={k:tup(v)for k,v in json.loads((INPUT/'h6.nodes.json').read_text()).items()}
inc=('leaf','inc',1)
assert ns6['node61']==((inc,'node60'),(inc,'node60'))
ns5=dict(ns6);ns5['node61']=((inc,'node60'),'node60')
assert ns5=={k:tup(v)for k,v in json.loads((ROOT/'machine/nodes.json').read_text()).items()}
ns4=dict(ns6);ns4['node61']=('node60','node60')
gq=c.read_grammar(INPUT/'q.grammar.json');gh=c.read_grammar(INPUT/'h6.grammar.json')
def code(nodes,g):
 c.raw_nodes=lambda:nodes
 sites,instructions,_=c.source(g)
 return json.loads(json.dumps(sites)),json.loads(json.dumps(instructions))
_,code6=code(ns6,gq);_,code5=code(ns5,gq);_,code4=code(ns4,gq)
assert code6==json.loads((INPUT/'qh6.instructions.json').read_text())
assert code5==json.loads((ROOT/'machine/instructions.json').read_text())
assert code(ns6,gh)[1]==json.loads((INPUT/'h6.instructions.json').read_text())
qnodes=dict(ns4);qnodes['node163']=('node6','node147')
assert code(qnodes,gq)[1]==json.loads((INPUT/'q.instructions.json').read_text())
def spans(nodes):
 count=0;found=[];constructors=[]
 def walk(t,path='',constructor=None):
  nonlocal count
  if isinstance(t,str):
   if t=='node65':constructor=path;constructors.append(path)
   lo=count
   if t=='node61':assert constructor is not None and path[len(constructor):]=='1110'
   walk(gq if t=='x67'else nodes[t],path,constructor)
   if t=='node61':found.append((lo,count))
  elif t[0]=='leaf':count+=1
  else:walk(t[0],path+'0',constructor);walk(t[1],path+'1',constructor)
 walk('node172')
 assert len(constructors)==len(found)==61
 return found,count
def relocation(old_nodes,new_nodes,old,new,kold,knew):
 so,no=spans(old_nodes);sn,nn=spans(new_nodes)
 mapping={};inside=set();a=b=0
 for(lo,ho),(ln,hn)in zip(so,sn):
  assert ho-lo==kold and hn-ln==knew and lo-a==ln-b
  for i in range(a,lo):mapping[i]=b+i-a
  mapping[lo]=ln;inside.update(range(lo,ho))
  for i in range(lo,ho):assert old[i]==['inc',1,i+1]
  for i in range(ln,hn):assert new[i]==['inc',1,i+1]
  a,b=ho,hn
 assert no-a==nn-b
 for i in range(a,no):mapping[i]=b+i-a
 for i,row in enumerate(old):
  if i in inside:continue
  split=2 if row[0]in('inc','dec')else 1
  assert all(t in mapping for t in row[split:]),('external interior entry',i,row)
  assert new[mapping[i]]==row[:split]+[mapping[t]for t in row[split:]],(i,row)
 return {'old_coefficient':kold,'new_coefficient':knew,'old_sites':no,
  'new_sites':nn,'constructor_blocks':61,'outside_sites_exactly_relocated':no-len(inside),
  'all_successor_targets_checked':True,'no_external_entry_into_block_interiors':True,
  'old_spans':so,'new_spans':sn,'entry_relocation':mapping}
r65=relocation(ns6,ns5,code6,code5,6,5)
r45=relocation(ns4,ns5,code4,code5,4,5)
assert(r65['old_sites'],r65['new_sites'],r45['old_sites'])==(3775,3714,3653)
assert r65['outside_sites_exactly_relocated']==r45['outside_sites_exactly_relocated']==3409
receipt={'status':'PASS','source_sites':3714,'constructors':61,
 'controller_and_Q_emitter_unchanged_from_QH6':True,
 'restoring_coefficient6_exactly_reproduces_QH6':True,
 'restoring_coefficient4_and_cached_MP_exactly_reproduces_Q':True,
 'six_to_five':r65,'four_to_five':r45,
 'physical_fixed_row_change':[190,1,[1,'R',330],[1,'R',99]],
 'scope':'Exact finite source binding. Logical equivalence uses the coefficient-five calibration and the supplied command compiler, not direct numeral trajectory equality.'}
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'proof/source_binding.json');a=p.parse_args()
a.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in('six_to_five','four_to_five')},indent=2))
