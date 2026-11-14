#!/usr/bin/env python3
"""Exact source binding for QN6, including all coefficient-six multiplier occurrences."""
from pathlib import Path
import json,sys,hashlib,argparse
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
INPUT=ROOT/'construction/inputs'
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns={k:tup(v)for k,v in json.loads((INPUT/'n6.nodes.json').read_text()).items()}
assert ns['node163']==('node6','node54')
assert ns['node170']==('node36','node169') and ns['node168']==('node37','node57')
inc=('leaf','inc',1)
assert ns['node61']==((inc,'node60'),(inc,'node60'))
gq=c.read_grammar(INPUT/'q.grammar.json');gn=c.read_grammar(INPUT/'n6.grammar.json')
def code(nodes,g):
 c.raw_nodes=lambda:nodes
 sites,ins,_=c.source(g)
 return json.loads(json.dumps(sites)),json.loads(json.dumps(ins))
def flatten(g):
 if isinstance(g,tuple)and len(g)==2:return flatten(g[0])+flatten(g[1])
 if g=='node60':return [inc]*2
 if g=='node61':raise AssertionError('unexpected coefficient multiplier as AX token')
 return[g]
wn=flatten(gn);wq=flatten(gq)
assert len(wn)==len(wq)==190
assert wn[:102]==wq[:102]and wn[121:]==wq[121:]and wn[102:121]!=wq[102:121]
ss6,code6=code(ns,gq)
assert code6==json.loads((ROOT/'machine/instructions.json').read_text())
assert code(ns,gn)[1]==json.loads((INPUT/'n6.instructions.json').read_text())
ns4=dict(ns);ns4['node61']=('node60','node60')
ss4,code4=code(ns4,gq)
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
sp4,n4=spans(ns4);sp6,n6=spans(ns)
assert(n4,n6)==(3654,3776)
mapping={};oldinside=set();newinside=set();a=b=0
for(l4,h4),(l6,h6)in zip(sp4,sp6):
 assert h4-l4==4 and h6-l6==6 and l4-a==l6-b
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
codeN=code(ns,gn)[1]
changes=[[i,a,b]for i,(a,b)in enumerate(zip(codeN,code6))if a!=b]
assert len(codeN)==len(code6)==3776 and len(changes)==83
receipt={'status':'PASS','Q_grammar_only_changes_macro_interval':[102,121],'macro_tokens':190,'N6_controller_nodes_unchanged':True,'no_push_MP_source':True,'sum_guard_source':True,'source4_sites':n4,'source6_sites':n6,'constructor_blocks':61,'each_replacement':['T += 4','T += 6'],'all_outside_multiplier_sites_exactly_relocated':n4-len(oldinside),'no_external_entry_into_block_interiors':True,'multiplier_relative_path':'1110','changed_instructions_from_N6':changes,'unchanged_instructions_from_N6':n6-len(changes),'spans4':sp4,'spans6':sp6,'scope':'Exact full source graph and generic multiplier bindings; source-language command mathematics and logical calibration are separate ordinary proofs.'}
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'proof/source_binding.json');a=p.parse_args()
a.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in('changed_instructions_from_N6','spans4','spans6')},indent=2))
