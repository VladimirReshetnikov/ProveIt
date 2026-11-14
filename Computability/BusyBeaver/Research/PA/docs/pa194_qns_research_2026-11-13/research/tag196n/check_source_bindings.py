#!/usr/bin/env python3
"""Audit scalar multiplication, no-push source, and unchanged arithmetic rows.
Does not import the builder and does not run its heuristic fold search.
"""
from pathlib import Path
import json,sys
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c
INC=('leaf','inc',1)
grammar=c.read_grammar(ROOT/'inputs/grammar.json')
base_nodes=c.raw_nodes();ns=dict(base_nodes)
ns['node163']=('node6','node54')
c.raw_nodes=lambda:ns
sites_original,ins_original,_=c.source(grammar)
ns=dict(ns);ns['node61']=(INC,(INC,'node60'))
c.raw_nodes=lambda:ns
sites,ins,_=c.source(grammar)
assert ins==ins_original
assert json.loads(json.dumps(ins))==json.loads((ROOT/'machine/instructions.json').read_text())
assert [[''.join(map(str,p)),op,a]for p,op,a in sites]==json.loads((ROOT/'machine/sites.json').read_text())
changed=[name for name in base_nodes if base_nodes[name]!=ns[name]]
assert changed==['node61','node163']
body_paths=[]
def walk(t,p):
 if isinstance(t,str):
  if t=='node61':body_paths.append(p)
  walk(grammar if t=='x67'else ns[t],p)
 elif c.isnode(t):walk(t[0],p+(0,));walk(t[1],p+(1,))
walk('node172',())
assert len(body_paths)==61
prefix=[('dec',2,8,1),('inc',7,2),('dec',6,4,3),('jump',7),
 ('dec',7,7,5),('inc',6,6),('jump',4),('jump',0),('dec',7,11,9),
 ('inc',2,10),('jump',8),('dec',1,15,12),('inc',7,13),('inc',6,14),
 ('jump',11),('dec',6,21,16),('inc',7,17),('dec',6,20,18),
 ('inc',1,19),('jump',17),('jump',11)]
starts=[]
for p in body_paths:
 ids=[i for i,(q,op,a)in enumerate(sites)if q[:len(p)]==p]
 assert ids==list(range(ids[0],ids[0]+4))
 first=ids[0];base=first-22
 got=[]
 for row in ins[base:base+21]:
  got.append(row[:2]+tuple(v-base for v in row[2:])if row[0]in('inc','dec')else('jump',row[1]-base))
 assert got==prefix
 assert all(ins[i]==('inc',1,i+1)for i in ids)
 assert ins[first-1]==('dec',7,first+5,first)
 assert ins[first+4]==('jump',first-1)
 starts.append(first)
def rows(path):
 return{tuple(map(int,line.split()[:2])):line.split()[2:]for line in path.read_text().splitlines()}
oldT=rows(ROOT/'inputs/base201.native.tm');newT=rows(ROOT/'machine/machine.native.tm')
assert all(newT[q,b]==oldT[q,b]for q in c.BOXSTATES for b in(0,1))
r={'passed':True,'source_sites':len(sites),'non_AX_node_changes':changed,
 'coefficient_four_reassociation_preserves_every_resolved_primitive_instruction':True,
 'literal_source_files_match_resolved_tree':True,'constructor_occurrences':len(starts),
 'all_constructor_prefixes_exact':True,'all_multiplication_bodies_exactly_four_increments':True,
 'arithmetic_box_rows_checked':2*len(c.BOXSTATES),'arithmetic_box_rows_unchanged':True,
 'multiplication_body_starts':starts}
(ROOT/'source_bindings_receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
