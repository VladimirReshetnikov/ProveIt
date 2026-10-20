#!/usr/bin/env python3
"""Independently reconstruct DP winners and check exact source obligations."""
from pathlib import Path
from functools import cache
import json,sys,hashlib
sys.dont_write_bytecode=True
import source_language as s
import build221 as b
import measure_pinned as m
P=Path(__file__).resolve().parent
plan=json.loads((P/'input.json').read_text());dp=json.loads((P/'dp-result.json').read_text())
seed=Path(plan['seed']);raw=(seed/'sites218.json').read_bytes();tab=(seed/'k218.native.tm').read_bytes()
assert m.sha(raw)==plan['seed_source_sha256'] and m.sha(tab)==plan['seed_table_sha256']
tree=s.tree(json.loads(raw));table=b.read_table(tab);oldrows=s.sites(tree);oldgraph=s.graph_arithmetic(oldrows)[0]
assert oldgraph==s.graph_intervals(oldrows)
base=[]
for row in plan['nodes']:
 base.append(tuple(row['leaf']) if 'leaf' in row else tuple(base[i] for i in row['children']))
macros={k:base[i] for k,i in plan['macro_ids'].items()}
def decode(w):
 stack=[]
 for c in w:
  if c in 'IQ':r,l=stack.pop(),stack.pop();stack.append((c,l,r))
  else:stack.append(c)
 assert len(stack)==1
 return stack[0]
def restore(x):return base[x] if type(x)==int else (restore(x[0]),restore(x[1]))
def map_old(i,delta):
 assert i<=135 or i>=486,('Outside edge enters changed interior',i)
 return i if i<=135 else i+delta
out=P/'verified';assert not out.exists();out.mkdir();results=[]
identity,im=m.compile_tree(s,b,table,tree,tree);assert identity==table
for k,c in enumerate(dp['candidates']):
 d=out/f'candidate{k:03}';d.mkdir()
 new=restore(c['replacement']);word=c['word'];recipe=plan['recipes'][word]
 assert ''.join(recipe['formula_postfix'])==word
 forms=[decode(w) for w in recipe['formula_postfix']]
 assert len(forms)==3
 ref=m.serial([macros[x] for x in word]);assert m.flat(new)==m.flat(ref) and s.boundary(new)==(0,0,False)
 whole=m.splice(s,tree,135,486,new);reference=m.splice(s,tree,135,486,ref)
 rows=s.sites(whole);rr=s.sites(reference);graph,nchecks=s.graph_arithmetic(rows);rg=s.graph_arithmetic(rr)[0]
 assert graph==s.graph_intervals(rows)==rg==s.graph_intervals(rr)
 assert m.flat(whole)==m.flat(tree)[:135]+m.flat(new)+m.flat(tree)[486:]
 delta=len(rows)-len(oldrows);outside=0
 for i,(eff,targets) in enumerate(oldgraph):
  if 135<=i<486:continue
  j=map_old(i,delta);assert graph[j]==[eff,[map_old(t,delta) for t in targets]],(i,j,graph[j],eff,targets)
  outside+=1
 met=s.metrics(whole)
 assert all(met[x]==c[x] for x in ('dag_nodes','maximum_depth','maximum_zero_run'))
 assert met['maximum_zero_run']<=6 and met['maximum_depth']<=64
 (d/'sites.json').write_bytes(s.compact(rows))
 rec={'status':'EXACT_CLOSED_SOURCE_CANDIDATE_PASS','source_metrics':met,'word':word,'recipe':recipe,'formula_outputs':forms,'AX_output_count':12,'closed_macro_sequence':True,'full_primitive_word_bound':True,'outside_guarded_edges_bound':outside,'two_full_CFG_resolvers':True,'reference_parse_CFG_equal':True,'decoder_successor_checks':nchecks,'initial37_source_paths_unchanged':rows[:37]==oldrows[:37],'source_sha256':m.sha(s.compact(rows)),'scope':'Source and exploratory allocator only; no startup, runtime or changed-machine calibration.'}
 if k<4:
  try:
   tt,cm=m.compile_tree(s,b,table,tree,whole);rec['compiler']=cm;(d/'raw.tm').write_bytes(b.table_bytes(tt))
  except (ValueError,AssertionError,KeyError) as e:rec['compiler_error']=repr(e)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec)
 print(k,met,rec.get('compiler',rec.get('compiler_error')),flush=True)
(P/'verified-result.json').write_text(json.dumps({'status':'DP_SOURCE_WINNERS_VERIFIED','candidate_count':len(results),'identity_compiler_control':im,'minimum_DAG':min(r['source_metrics']['dag_nodes'] for r in results),'results':results,'no_runtime':True},indent=2)+'\n')
