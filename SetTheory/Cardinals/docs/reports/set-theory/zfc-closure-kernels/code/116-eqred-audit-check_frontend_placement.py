#!/usr/bin/env python3
"""Inspect saved source AST placement, independently of cost-report assertions."""
from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent
P=OUT/'frontend_snapshots'
def need(x,m):
 if not x:raise ValueError(m)
def V(r):return isinstance(r,list) and len(r)==3 and r[0]=='imp' and r[1] in ('a','b','c') and r[2]==['all',r[1],r[1]]
def conjparts(f):
 if isinstance(f,list) and len(f)==3 and f[0]=='imp' and f[2]==1:
  t=f[1]
  if isinstance(t,list) and len(t)==3 and t[0]=='imp':
   u=t[2]
   if isinstance(u,list) and len(u)==3 and u[0]=='imp' and u[2]==1:return conjparts(t[1])+conjparts(u[1])
 return [f]
reports={}
for name in ('omit_equality_deep','omit_equality_cost','symmetry_canonical_cost','symmetry_canonical_warm'):
 fn=P/name/'source.json';d=json.loads(fn.read_text());rows=d['rows'];where=[i for i,r in enumerate(rows) if V(r)]
 need(len(where)==1,('one positive V row',name))
 parts=conjparts(d['bundle']);rv=['imp',['rel','a','b'],['all','c',['rel','a','b']]]
 need(len(parts)==3 and parts.count(rv)==1,('three bundle components including Rel-vacuity',name))
 reports[name]={'source_sha256':hashlib.sha256(fn.read_bytes()).hexdigest(),'positive_V_row_index_including_GEN':where[0],'positive_V_row':rows[where[0]],'negative_bundle_component_count':len(parts),'Rel_vacuity_component_present':True,'scope':'AST placement only; not an independent runtime or enumerator-coverage verification.'}
(OUT/'frontend_placement_results.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports,indent=2))
