#!/usr/bin/env python3
"""Independently resolve the complete CFG and check the one AX-exit splice."""
from pathlib import Path
import argparse,json,sys,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'qh5_reference/verification/reference'))
import source_language as lang
def graph(sites):
 tags={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
 mapped=[[p,tags[op],a] for p,op,a in sites]
 g,_=lang.graph_arithmetic(mapped);assert g==lang.graph_intervals(mapped)
 names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
 return [[names[e[0]]]+e[1:]+targets for e,targets in g]
def expand_grammar(path):
 d=json.loads(path.read_text())
 def rec(t):
  if isinstance(t,str)and t in d['rules']:return [rec(x)for x in d['rules'][t]]
  return t
 return rec(d['root'])
def sites_of(grammar,nodes):
 sites=[];visits={}
 def walk(t,p):
  if isinstance(t,str):
   visits.setdefault(t,[]).append(p);walk(grammar if t=='x67'else nodes[t],p)
  elif t[0]=='leaf':sites.append([p,t[1],t[2]])
  else:
   assert len(t)==2;walk(t[0],p+'0');walk(t[1],p+'1')
 walk('node172','');return sites,visits
def check(machine,reference):
 nodes=json.loads((machine/'nodes.json').read_text())
 assert nodes==json.loads((reference/'machine/nodes.json').read_text())
 oldg=expand_grammar(reference/'construction/inputs/q.grammar.json')
 newg=expand_grammar(machine/'grammar.json')
 changed=[]
 def replace(t,p=''):
  if t==['leaf','breakTo',1]:changed.append(p);return 'node49'
  return [replace(t[0],p+'0'),replace(t[1],p+'1')]if isinstance(t,list)and len(t)==2 else t
 assert replace(oldg)==newg and len(changed)==1
 old,ov=sites_of(oldg,nodes);new,nv=sites_of(newg,nodes)
 assert old==json.loads((reference/'machine/sites.json').read_text())
 assert new==json.loads((machine/'sites.json').read_text())
 oi,ni=graph(old),graph(new)
 assert oi==json.loads((reference/'machine/instructions.json').read_text())
 assert ni==json.loads((machine/'instructions.json').read_text())
 assert len(ov['x67'])==1
 p=ov['x67'][0]+changed[0]
 removed=next(i for i,x in enumerate(old)if x[0]==p)
 assert old[removed][1:]==['breakTo',1]
 inserted=[i for i,x in enumerate(new)if x[0].startswith(p)]
 assert len(inserted)==19 and inserted==list(range(min(inserted),max(inserted)+1))
 lookup={x[0]:j for j,x in enumerate(new)}
 relocation={i:lookup[x[0]]for i,x in enumerate(old)if i!=removed}
 def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else[]
 def project(row):
  n=2 if row[0]in('inc','dec')else 1
  return row[:n]+[min(inserted)if t==removed else relocation[t]for t in row[n:]]
 for i,j in relocation.items():assert project(oi[i])==ni[j],(i,j)
 # Compare to a pre-existing node49 push with its outside successor abstracted.
 reference_path=next(q for q in ov['node49']if not q.startswith(ov['x67'][0]))
 original_push=[i for i,x in enumerate(old)if x[0].startswith(reference_path)]
 assert len(original_push)==19
 localmap=dict(zip(original_push,inserted))
 for i,j in localmap.items():
  row=oi[i];n=2 if row[0]in('inc','dec')else 1
  newtargets=[]
  for t in row[n:]:
   if t in localmap:newtargets.append(localmap[t])
   else:
    assert t==max(original_push)+1
    newtargets.append(max(inserted)+1)
  assert row[:n]+newtargets==ni[j],(i,j)
 for i,row in enumerate(ni):
  if i in inserted:continue
  for t in targets(row):
   if t in inserted:assert t==min(inserted)
 assert max(inserted)+1==relocation[removed+1]
 assert old[25]==new[25] and relocation[25]==25
 return dict(status='PASS',old_sites=len(old),new_sites=len(new),unchanged_sites=len(relocation),removed_AX_break_site=removed,inserted_push_sites=inserted,old_break_target=oi[removed][1],new_following_MP_field_reader=relocation[removed+1],nodes_unchanged=True,exact_single_grammar_splice=True,push_matches_existing_resolved_19_site_CFG=True,outside_CFG_edges_preserved=True,no_external_entry_into_push_interior=True,seed_site_unchanged=True,independent_arithmetic_and_interval_resolvers_agree=True,relocation=relocation)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,default=ROOT/'AX11QH5');p.add_argument('--reference',type=Path,default=ROOT/'qh5_reference');p.add_argument('--output',type=Path,default=ROOT/'AX11QH5/source_binding.json');a=p.parse_args()
 result=check(a.machine,a.reference);a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='relocation'},indent=2))
