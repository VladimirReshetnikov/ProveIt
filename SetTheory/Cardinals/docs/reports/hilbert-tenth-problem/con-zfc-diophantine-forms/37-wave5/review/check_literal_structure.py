#!/usr/bin/env python3
"""Independent syntax, variable, liveness and binary-gate audit of literal outputs.
This does not import any builder and does not claim semantic/kernel verification.
"""
from pathlib import Path
import json,collections
ROOT=Path(__file__).resolve().parents[1]
FILES=['signed/generated/signed14.json','signed/generated/signed15.json','signed/generated/signed16.json','nine/generated/nine_sharp_natural.json','nine/generated/nine_sharp_positive.json','positive/shift_half_product.json','positive/short_plain_product.json','lowdegree/integer24_ratio_product.json','lowdegree/integer50_quartic.json']
rows=[]
for path in FILES:
 d=json.loads((ROOT/path).read_text()); variables=d.get('variables',d.get('witnesses')); assert len(set(variables))==len(variables)
 if 'nodes' in d:
  nodes=d['nodes']; seen=set(); counts=collections.Counter();varseen=set();fixed=set()
  def visit(i):
   assert type(i) is int and 0<=i<len(nodes)
   if i in seen:return
   seen.add(i);n=nodes[i];k=n['kind']
   if k in ('add','sub','mul'):
    assert n['left']<i and n['right']<i;counts[k]+=1;visit(n['left']);visit(n['right'])
   elif k=='literal':assert type(n['value']) is int
   elif k=='fixed':fixed.add(n['name'])
   elif k=='variable':varseen.add(n['name'])
   else:raise AssertionError(k)
  visit(d['output']);assert len(seen)==len(nodes);assert set(variables)==varseen
  assert dict(counts)==d['operation_counts']
  row={'file':path,'variables':len(variables),'operations':sum(counts.values()),'operations_by_type':dict(counts),'fixed_leaves':len(fixed),'all_nodes_live':True,'all_variables_live':True}
 else:
  src=d['source'];positions={};counts=collections.Counter();inputs=set(variables);fixed=d['fixed_numerals'];fixed=set(fixed) if isinstance(fixed,dict) else set(fixed)
  for i,(name,op,a,b) in enumerate(src):
   assert name not in positions and name not in inputs and name not in fixed
   assert op in ('+','-','*')
   for arg in (a,b):assert type(arg) is int or arg in positions or arg in inputs or arg in fixed,(path,arg)
   positions[name]=i;counts[op]+=1
  seen=set();used=set()
  def visit(name):
   if type(name) is int or name in fixed:return
   if name in inputs:used.add(name);return
   if name in seen:return
   seen.add(name);_,_,a,b=src[positions[name]];visit(a);visit(b)
  visit(d['output']);assert len(seen)==len(src);assert used==inputs
  assert sum(counts.values())==d['ledger']['operations']
  row={'file':path,'variables':len(variables),'operations':sum(counts.values()),'operations_by_type':dict(counts),'fixed_leaves':len(fixed),'all_nodes_live':True,'all_variables_live':True}
 rows.append(row)
result={'status':'pass','scope':'Independent literal artifact structural checks only; no builder imports','artifacts':rows}
(ROOT/'review/LITERAL_STRUCTURE_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
