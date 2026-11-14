#!/usr/bin/env python3
"""Exact source equality to PA194H with all 61 multiplier blocks widened 4->6."""
from pathlib import Path
import json,sys,hashlib,argparse
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns={k:tup(v)for k,v in json.loads((ROOT/'machine/nodes.json').read_text()).items()}
parent={k:tup(v)for k,v in json.loads((ROOT/'construction/inputs/parent6.nodes.json').read_text()).items()}
changes={k:[parent[k],ns[k]]for k in ns if ns[k]!=parent[k]}
assert set(changes)=={'node163','node170'}
assert ns['node163']==('node6','node54')
assert ns['node170']==(('node36',('node167','node145')),'node57')
g=c.read_grammar(ROOT/'construction/inputs/pa194.grammar.json')

def get_code(nodes):
 c.raw_nodes=lambda:nodes
 sites,ins,_=c.source(g)
 return json.loads(json.dumps(sites)),json.loads(json.dumps(ins))

def spans(nodes):
 count=0;found=[]
 def walk(t):
  nonlocal count
  if isinstance(t,str):
   lo=count
   walk(g if t=='x67'else nodes[t])
   if t=='node61':found.append((lo,count))
  elif t[0]=='leaf':count+=1
  else:walk(t[0]);walk(t[1])
 walk('node172')
 return found,count

def multiplier_occurrences():
 found=[]
 def walk(t,path,constructor_path=None):
  if isinstance(t,str):
   if t=='node65':constructor_path=path
   if t=='node61':
    assert constructor_path is not None and path[len(constructor_path):]=='1110'
    found.append(path)
   walk(g if t=='x67'else ns[t],path,constructor_path)
  elif t[0]!='leaf':
   walk(t[0],path+'0',constructor_path);walk(t[1],path+'1',constructor_path)
 walk('node172','')
 assert len(found)==61
 return found
locations=multiplier_occurrences()
oldnodes=dict(ns);oldnodes['node61']=('node60','node60')
ss4,code4=get_code(oldnodes);ss6,code6=get_code(ns)
assert code4==json.loads((ROOT/'construction/inputs/pa194H.instructions.json').read_text())
assert code6==json.loads((ROOT/'machine/instructions.json').read_text())
sp4,n4=spans(oldnodes);sp6,n6=spans(ns)
assert len(sp4)==len(sp6)==61 and n4==3653 and n6==3775
mapping={};oldinside=set();newinside=set()
a=b=0
for (l4,h4),(l6,h6)in zip(sp4,sp6):
 assert h4-l4==4 and h6-l6==6
 assert l4-a==l6-b
 for i in range(a,l4):mapping[i]=b+i-a
 mapping[l4]=l6
 oldinside.update(range(l4,h4));newinside.update(range(l6,h6))
 for i in range(l4,h4):assert code4[i]==['inc',1,i+1]
 for i in range(l6,h6):assert code6[i]==['inc',1,i+1]
 a,b=h4,h6
assert n4-a==n6-b
for i in range(a,n4):mapping[i]=b+i-a
for i,row in enumerate(code4):
 if i in oldinside:continue
 split=2 if row[0]in('inc','dec')else 1
 assert all(t in mapping for t in row[split:]),('entry into multiplier interior',i,row)
 assert code6[mapping[i]]==row[:split]+[mapping[t]for t in row[split:]],(i,row)
receipt={'status':'PASS','source4_equals_supplied_PA194H':True,'source4_sites':n4,'source6_sites':n6,'constructor_blocks':61,'every_multiplier_belongs_to_node65':True,'multiplier_relative_path':'1110','each_replacement':{'old':'T += 4','new':'T += 6'},'all_outside_sites_exactly_relocated':n4-len(oldinside),'no_external_entry_into_block_interiors':True,'spans4':sp4,'spans6':sp6,'node_edits_from_radix6_parent':changes,'scope':'Exact CFG statement; generic constructor and logical radix calibration are separately proved in the mathematical references.'}
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'proof/source_binding.json');args=parser.parse_args()
args.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if not k.startswith('spans')},indent=2))
