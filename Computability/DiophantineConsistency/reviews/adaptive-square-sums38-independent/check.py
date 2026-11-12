#!/usr/bin/env python3
"""Independent exact DAG/mapping/degree audit; no Lean, generation or staging."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'parent':('research/adaptive-square-sums40-quotient-quartic/candidate.json','fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d'),
 'child':('research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'),
 'natural':('research/adaptive-square-sums38-two-quadratic-products/natural-candidate.json','c8fd12460715a24c354758c50d7cf1dd13df5ecd86031c836424ba000fee7aec'),
 'author_receipt':('research/adaptive-square-sums38-two-quadratic-products/result.json','c480e61fd1a90a57ebc6fcb984f47eed7354d561c8b15dc0edf20934fa24e994'),
 'parent_literal':('Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece'),
 'parent_native':('Lean/DiophantineConsistency/IPRAQM40Native.lean','d261c83bf10cd406063b6622b477dac4aefe0a811f1e471ad5142e587864d40b'),
 'parent_standard':('research/ipra-standard-qm40/draft/IPRAStandardQM40.lean','f08d26c6eee7dc79c89693da0848d58f36abac0a027e611804944ccaeb76acda')}
b={}
for n,(p,h) in files.items():
 raw=(D/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==h,n;b[n]=raw.decode()
old,new,nat=map(json.loads,(b['parent'],b['child'],b['natural']))
assert old['operations']==len(old['source'])==166 and len(old['witnesses'])==40
assert new['operations']==len(new['source'])==160 and len(new['witnesses'])==38
assert nat['operations']==len(nat['source'])==198 and len(nat['witnesses'])==38
assert new['intended_domain']=='positive integers' and nat['intended_domain']=='nonnegative integers'
assert new['witnesses']==[n for n in old['witnesses'] if n not in {'ellProductVariable','deltaProductVariable'}]
assert new['fixed_numerals']==old['fixed_numerals'] and new['output']==old['output']
a={r[0]:r for r in old['source']};z={r[0]:r for r in new['source']}
assert len(a)==166 and len(z)==160
assert set(a)-set(z)=={'ellProductDifference','ellProductConstraint','add_ellProduct','deltaProductDifference','deltaProductConstraint','add_deltaProduct'} and not set(z)-set(a)
assert [r[0] for r in new['source']]==[r[0] for r in old['source'] if r[0] in z]
changed={n for n in z if z[n]!=a[n]}
assert changed=={'g41','g64','add_scaledIndex','add_rankSeed'}
assert z['g41']==['g41','+',1,'g40'] and z['g64']==['g64','+',1,'g63']
assert z['add_scaledIndex']==['add_scaledIndex','+','add_product2','scaledIndexConstraint']
assert z['add_rankSeed']==['add_rankSeed','+','add_qSigned','rankSeedConstraint']
assert z['g30']==['g30','+','ellVariable','k'] and z['k']==['k','+','eta','zeta']
assert z['g40']==['g40','*','ellVariable','g30'] and z['g63']==['g63','*','deltaVariable','cSquareVariable']
assert a['ellProductDifference']==['ellProductDifference','-','ellProductVariable','g40']
assert a['deltaProductDifference']==['deltaProductDifference','-','deltaProductVariable','g63']
# Check exact Lean parent literal source rows, not merely a module name.
text=b['parent_literal'];part=text.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n',1)[1].split('\ntheorem literal_eq ',1)[0]
expected=[f'  let {n} : Expr (Fin 40) := .var {i}' for i,n in enumerate(old['witnesses'])]
expected += [f'  let {n} : Expr (Fin 40) := .constant (p {i})' for i,n in enumerate(old['fixed_numerals'])]
expected += [f'  let {n} := {x} {op} {y}' for n,op,x,y in old['source']]
expected += ['  '+old['output']]
assert part.splitlines()==expected
assert '(positiveShift (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports))' in b['parent_native']
assert 'IPRAQM40Native.literal_equivalence' in b['parent_standard']
# Every graph row is topological, names are unique, and every row and input is live.
def check_graph(g):
 known=set(g['witnesses']+g['fixed_numerals']);assert len(known)==len(g['witnesses'])+len(g['fixed_numerals'])
 rows={}
 for n,op,x,y in g['source']:
  assert n not in known and op in ('+','-','*') and all(type(v)==int or v in known for v in (x,y))
  rows[n]=(op,x,y);known.add(n)
 todo=[g['output']];seen=set(todo)
 while todo:
  n=todo.pop()
  if n in rows:
   for v in rows[n][1:]:
    if isinstance(v,str) and v not in seen:seen.add(v);todo.append(v)
 assert set(rows)<=seen and set(g['witnesses'])<=seen and set(g['fixed_numerals'])<=seen
 return rows,Counter(op for n,op,x,y in g['source'])
parentrows,_=check_graph(old);childrows,posops=check_graph(new);_,natops=check_graph(nat)
# Exact shift from 38 naturals to 38 positive variables, preserving ports.
assert nat['witnesses']==['n_'+n for n in new['witnesses']]
assert nat['fixed_numerals']==new['fixed_numerals'] and nat['output']==new['output']
shiftrows=[['shift_'+n,'+','n_'+n,1] for n in new['witnesses']]
def shift(v):return 'shift_'+v if isinstance(v,str) and v in new['witnesses'] else v
assert nat['source']==shiftrows+[[n,op,shift(x),shift(y)] for n,op,x,y in new['source']]
# Extract the actual output sum, treating each square gate as an independent
# formal token. This catches missing, duplicated and cross-wired residuals.
def sums(g,rows):
 squares={n:x for n,(op,x,y) in rows.items() if op=='*' and x==y and isinstance(x,str) and (n.endswith('Constraint') or n in {'firstSquare','mainSquare','auxSquare','strongSquare'})}
 def go(n):
  if n in squares:return Counter({n:1})
  assert n in rows and rows[n][0]=='+',n
  x,y=rows[n][1:];return go(x)+go(y)
 used=go(g['output']);assert set(used)==set(squares) and set(used.values())=={1}
 return squares
oldSq=sums(old,parentrows);newSq=sums(new,childrows)
assert len(oldSq)==31 and len(newSq)==29
assert set(oldSq)-set(newSq)=={'ellProductConstraint','deltaProductConstraint'}
assert all(oldSq[n]==r for n,r in newSq.items())
# Sparse exact integer polynomials in all 38 witnesses and four formal ports.
def add(p,q,sgn=1):
 r=dict(p)
 for m,c in q.items():r[m]=r.get(m,0)+sgn*c
 return {m:c for m,c in r.items() if c}
def mul(p,q):
 r={}
 for a,c in p.items():
  for b,d in q.items():
   k=tuple(sorted(a+b));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items() if c}
def evaluate(g,targets,sub=None):
 rows={n:(o,x,y) for n,o,x,y in g['source']};need=set(targets);todo=list(targets)
 while todo:
  n=todo.pop()
  if n in rows:
   for v in rows[n][1:]:
    if isinstance(v,str) and v not in need:need.add(v);todo.append(v)
 env={n:{(n,):1} for n in g['witnesses']+g['fixed_numerals']};env.update(sub or {})
 for n,op,x,y in g['source']:
  if n not in need:continue
  x=({():x} if x else {}) if type(x)==int else env[x]
  y=({():y} if y else {}) if type(y)==int else env[y]
  env[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 return env
residuals=list(newSq.values());child=evaluate(new,residuals+['g40','g63'])
sub={'ellProductVariable':child['g40'],'deltaProductVariable':child['g63']}
parent=evaluate(old,list(oldSq.values()),sub)
assert all(child[r]==parent[r] for r in residuals)
assert parent['ellProductDifference']=={} and parent['deltaProductDifference']=={}
unknown=set(new['witnesses'])
def degree(poly):return max((sum(x in unknown for x in m) for m in poly),default=-1)
assert all(degree(child[r])<=2 for r in residuals)
# No other residual contains firstQuotient², so the total sum has coefficient
# exactly 1 on firstQuotient⁴, for every specialization of the four ports.
for r in residuals:
 terms={tuple(x for x in m if x not in unknown):v for m,v in child[r].items() if tuple(x for x in m if x in unknown)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if r=='A0' else {}),(r,terms)
assert dict(posops)=={'*':71,'+':46,'-':43} and dict(natops)=={'*':71,'+':84,'-':43}
# A bounded check of the author's direct single-substitution scan, with ports
# kept formal. This is not an optimization or minimality proof.
pairs=[(x,y,n) for n,(op,x,y) in childrows.items() if n.endswith('Difference') and op=='-' and x in unknown]
assert len(pairs)==23
scan={}
for v,definition,dropped in pairs:
 value=evaluate(new,[definition])[definition]
 assert not any(v in m for m in value)
 remaining=[r for r in residuals if r!=dropped]
 polys=evaluate(new,remaining,{v:value})
 higher={r:degree(polys[r]) for r in remaining if degree(polys[r])>2}
 assert higher,(v,definition)
 scan[v]={'definition':definition,'removed_residual':dropped,'higher_degree_residuals':higher}
assert scan==json.loads(b['author_receipt'])['direct_single_substitution_scan']
print(json.dumps({'scope':'independent exact source/DAG/ring-polynomial review; no Lean, axiom or model proof',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'positive_witnesses':38,'positive_live_operations':160,'positive_ops_by_kind':dict(sorted(posops.items())),
 'natural_witnesses':38,'natural_live_operations':198,'natural_ops_by_kind':dict(sorted(natops.items())),
 'parent_residuals':len(oldSq),'child_residuals':len(newSq),'exact_quartic_coefficient_firstQuotient_four':1,
 'all_29_residuals_match_parent_after_lift':True,'removed_residuals_vanish_after_lift':True,
 'zero_map_lift_values':['ellVariable*(ellVariable+eta+zeta)','deltaVariable*cSquareVariable'],
 'common_coefficient_source':'CurrentWindowCarry2011.ports',
 'direct_single_substitutions_checked':len(scan),'formal_port_scan_not_global_minimality':True, 'lean_elaboration':False},sort_keys=True,indent=2))
