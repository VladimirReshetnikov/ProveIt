#!/usr/bin/env python3
"""Exact DAG, sum-of-squares, zero-map and degree checks; no Lean."""
from pathlib import Path
import hashlib,json,sys
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
oldraw=pin(D/'research/adaptive-square-sums40-quotient-quartic/candidate.json','fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d');old=json.loads(oldraw)
newraw=pin(P/'candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56');new=json.loads(newraw)
nat=json.loads(pin(P/'natural-candidate.json','c8fd12460715a24c354758c50d7cf1dd13df5ecd86031c836424ba000fee7aec'))
source=pin(D/'Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece').decode()
native=pin(D/'Lean/DiophantineConsistency/IPRAQM40Native.lean','d261c83bf10cd406063b6622b477dac4aefe0a811f1e471ad5142e587864d40b').decode()
standard=pin(D/'research/ipra-standard-qm40/draft/IPRAStandardQM40.lean','f08d26c6eee7dc79c89693da0848d58f36abac0a027e611804944ccaeb76acda').decode()
assert old['operations']==len(old['source'])==166 and len(old['witnesses'])==40
start=source.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=\n');end=source.index('\ntheorem literal_eq ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 40) :=']
expected += [f'  let {n} : Expr (Fin 40) := .var {i}' for i,n in enumerate(old['witnesses'])]
expected += [f'  let {n} : Expr (Fin 40) := .constant (p {i})' for i,n in enumerate(old['fixed_numerals'])]
expected += [f'  let {n} := {a} {o} {b}' for n,o,a,b in old['source']]
expected += ['  '+old['output']]
assert source[start:end].splitlines()==expected
assert '(AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)' in native
assert 'IPRAQM40Native.literal_equivalence' in standard and 'literal_iff_translated_consistency' in standard
# Literal elimination and output wiring; no reliance on sample evaluations.
removed={'ellProductDifference','ellProductConstraint','add_ellProduct','deltaProductDifference','deltaProductConstraint','add_deltaProduct'}
replacements={'g41':['g41','+',1,'g40'],'g64':['g64','+',1,'g63'],
 'add_scaledIndex':['add_scaledIndex','+','add_product2','scaledIndexConstraint'],
 'add_rankSeed':['add_rankSeed','+','add_qSigned','rankSeedConstraint']}
assert new['source']==[replacements.get(r[0],r) for r in old['source'] if r[0] not in removed]
assert new['witnesses']==[x for x in old['witnesses'] if x not in {'ellProductVariable','deltaProductVariable'}]
assert new['fixed_numerals']==old['fixed_numerals'] and new['output']==old['output']
assert new['operations']==len(new['source'])==160 and len(new['witnesses'])==38
oldrows={r[0]:r for r in old['source']};nr={r[0]:r for r in new['source']}
for n,r in {'g30':['g30','+','ellVariable','k'],'k':['k','+','eta','zeta'],
 'g40':['g40','*','ellVariable','g30'],'g63':['g63','*','deltaVariable','cSquareVariable'],
 'ellProductDifference':['ellProductDifference','-','ellProductVariable','g40'],
 'deltaProductDifference':['deltaProductDifference','-','deltaProductVariable','g63']}.items():assert oldrows[n]==r
# Check the natural shift exactly and verify source graph liveness/topology.
ren={n:'n_'+n for n in new['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert nat['witnesses']==[ren[x] for x in new['witnesses']]
assert nat['source']==[['shift_'+n,'+',ren[n],1] for n in new['witnesses']]+[[n,o,rep(a),rep(b)] for n,o,a,b in new['source']]
assert nat['operations']==len(nat['source'])==198 and len(nat['witnesses'])==38
assert nat['fixed_numerals']==new['fixed_numerals'] and nat['output']==new['output']
def live(g):
 known=set(g['witnesses']+g['fixed_numerals']);rows={}
 for n,o,a,b in g['source']:
  assert n not in known and o in ('+','-','*') and all(isinstance(x,int) or x in known for x in (a,b))
  known.add(n);rows[n]=(a,b)
 needed={g['output']};todo=[g['output']]
 while todo:
  n=todo.pop()
  for x in rows.get(n,()):
   if isinstance(x,str) and x not in needed:needed.add(x);todo.append(x)
 assert set(rows)<=needed and set(g['witnesses'])<=needed and set(g['fixed_numerals'])<=needed
 return Counter(r[1] for r in g['source'])
posops=live(new);natops=live(nat)
# Sparse exact polynomials in all inputs and formal port parameters.
def add(a,b,sign=1):
 out=dict(a)
 for mon,c in b.items():out[mon]=out.get(mon,0)+sign*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
 return {m:c for m,c in out.items() if c}
def con(n):return {():n} if n else {}
def eval_targets(g,targets,sub=None):
 rows={n:(o,a,b) for n,o,a,b in g['source']};need=set(targets);todo=list(targets)
 while todo:
  n=todo.pop()
  if n in rows:
   for x in rows[n][1:]:
    if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
 env={x:{(x,):1} for x in g['witnesses']+g['fixed_numerals']};env.update(sub or {})
 for n,o,a,b in g['source']:
  if n not in need:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 return env
res=['A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','ellProductDifference','scaledIndexDifference','ySquareDifference','qSignedDifference','deltaProductDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','gammaProductDifference','timeProductDifference']
dropped={'ellProductDifference','deltaProductDifference'};keep=[x for x in res if x not in dropped];assert len(keep)==29
child=eval_targets(new,keep+['g40','g63']);parent=eval_targets(old,res,{'ellProductVariable':child['g40'],'deltaProductVariable':child['g63']})
assert all(parent[x]==child[x] for x in keep) and all(parent[x]=={} for x in dropped)
# The whole output is exactly the sum of the 29 surviving residual squares.
def square_sum_shape(g,residuals):
 env={r:{(r,):1} for r in residuals}
 for n,o,a,b in g['source']:
  if n in env:continue
  if isinstance(a,str) and a not in env:continue
  if isinstance(b,str) and b not in env:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 expected={(r,r):1 for r in residuals}
 assert env[g['output']]==expected
square_sum_shape(old,res);square_sum_shape(new,keep)
w=set(new['witnesses'])
def degree(p):return max((sum(x in w for x in m) for m in p),default=-1)
assert all(degree(child[r])<=2 for r in keep)
# The only residual containing firstQuotient² is A0, with coefficient 1.
for r in keep:
 terms={tuple(x for x in mon if x not in w):co for mon,co in child[r].items() if tuple(x for x in mon if x in w)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if r=='A0' else {}),(r,terms)
# Exhaust all 23 remaining direct defining substitutions, with formal port
# parameters. Each raises at least one surviving residual's formal degree.
childrows={n:(o,a,b) for n,o,a,b in new['source']}
pairs=[(a,b,n) for n,(o,a,b) in childrows.items() if n.endswith('Difference') and o=='-' and a in w]
assert len(pairs)==23
scan={}
for variable,definition,drop in pairs:
 init=eval_targets(new,[definition])[definition]
 assert not any(variable in mon for mon in init)
 other=[r for r in keep if r!=drop];ev=eval_targets(new,other,{variable:init})
 bad={r:degree(ev[r]) for r in other if degree(ev[r])>2}
 assert bad,(variable,definition)
 scan[variable]={'definition':definition,'removed_residual':drop,'higher_degree_residuals':bad}
print(json.dumps({'scope':'exact graph/source/transformation and formal polynomial certificate; no Lean or full endpoint proof',
 'parent_positive':{'variables':40,'operations':166,'residuals':31},
 'child_positive':{'variables':38,'operations':160,'residuals':29,'degree':4,'operations_by_kind':dict(sorted(posops.items()))},
 'child_natural_shift':{'variables':38,'operations':198,'degree':4,'operations_by_kind':dict(sorted(natops.items()))},
 'zero_map_removed_values':['ellVariable*(ellVariable+eta+zeta)','deltaVariable*cSquareVariable'],
 'all_29_residuals_exact_after_lift':True,'firstQuotient_fourth_coefficient':1,
 'direct_single_substitution_scan':scan,'formal_port_scan_not_specialized':True,
 'parent_lean_literal_rows_match':True,'new_lean_elaboration':False},sort_keys=True,indent=2))
