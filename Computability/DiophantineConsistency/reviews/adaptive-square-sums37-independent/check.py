#!/usr/bin/env python3
"""Independent exact DAG/residual/degree review; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'parent':('research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'),
 'child':('research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'),
 'natural':('research/adaptive-square-sums37-difference-quartic/natural-candidate.json','a6660fea4eb44a9cf2aeed92b7a16bd0b76af5410a275feaceb0661f82509c1a'),
 'author_receipt':('research/adaptive-square-sums37-difference-quartic/result.json','07ede5d8f22e400be9dd6ad478c8bc55281925d27edfd1e2b5f03bf41a7394be'),
 'parent_review':('reviews/adaptive-square-sums38-independent/result.json','5173a65bc0dd0140de5995e014929ad00fb05c0446b3367222ce8b6e6743aaff'),
 'model_ring':('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')}
data={}
for n,(p,h) in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;data[n]=b.decode()
par,g,nat=map(json.loads,(data['parent'],data['child'],data['natural']))
assert par['intended_domain']==g['intended_domain']=='positive integers' and nat['intended_domain']=='nonnegative integers'
assert len(par['witnesses'])==38 and len(g['witnesses'])==len(nat['witnesses'])==37
assert g['witnesses']==['differencePlusOne' if x=='squareVariable' else x for x in par['witnesses'] if x!='ySquareVariable']
assert g['fixed_numerals']==par['fixed_numerals']==nat['fixed_numerals'] and par['output']==g['output']==nat['output']
# Reconstruct exact source edits by names, including sum-chain rewiring.
removed={'ySquareDifference','ySquareConstraint','add_ySquare'}
changes={'g81':['g81','-','y2','g80'],'g82':['g82','*','qValueVariable','diffMinusOne'],
 'Fa':['Fa','-','y2','g82'],'squareDifference':['differenceEquality','-','diffMinusOne','g81'],
 'squareConstraint':['differenceConstraint','*','differenceEquality','differenceEquality'],
 'sumWithConstraint':['sumWithConstraint','+','sumSquares','differenceConstraint'],
 'add_qSigned':['add_qSigned','+','add_scaledIndex','qSignedConstraint']}
expected=[]
for row in par['source']:
 if row[0] in removed:continue
 if row[0]=='g82':expected.append(['diffMinusOne','-','differencePlusOne',1])
 expected.append(changes.get(row[0],row))
assert expected==g['source'] and len(g['source'])==g['operations']==158
shifts=[['shift_'+n,'+','n_'+n,1] for n in g['witnesses']]
def shift(x):return 'shift_'+x if isinstance(x,str) and x in g['witnesses'] else x
assert nat['witnesses']==['n_'+n for n in g['witnesses']]
assert nat['source']==shifts+[[n,o,shift(x),shift(y)] for n,o,x,y in g['source']]
assert len(nat['source'])==nat['operations']==195
def graph(G):
 seen=set(G['witnesses']+G['fixed_numerals']);rows={}
 for n,o,x,y in G['source']:
  assert n not in seen and o in ('+','-','*') and all(type(v)==int or v in seen for v in (x,y));seen.add(n);rows[n]=(o,x,y)
 active={G['output']};todo=list(active)
 while todo:
  n=todo.pop()
  if n in rows:
   for v in rows[n][1:]:
    if isinstance(v,str) and v not in active:active.add(v);todo.append(v)
 assert set(rows)<=active and set(G['witnesses']+G['fixed_numerals'])<=active
 return rows,Counter(row[1] for row in G['source'])
pr,_=graph(par);cr,ops=graph(g);_,nops=graph(nat)
def squares(G,rows):
 sq={n:x for n,(o,x,y) in rows.items() if o=='*' and x==y and isinstance(x,str) and (n.endswith('Constraint') or n in {'firstSquare','mainSquare','auxSquare','strongSquare'})}
 def traverse(n):
  if n in sq:return Counter({n:1})
  assert rows[n][0]=='+',n
  return traverse(rows[n][1])+traverse(rows[n][2])
 used=traverse(G['output']);assert set(used)==set(sq) and set(used.values())=={1}
 return sq
ps=squares(par,pr);cs=squares(g,cr);assert len(ps)==29 and len(cs)==28
# Sparse exact integer polynomial evaluation in witnesses and formal ports.
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def var(x):return {(x,):1}
def ev(G,targets,subst=None):
 rows={n:(o,a,b) for n,o,a,b in G['source']};needed=set(targets);todo=list(targets)
 while todo:
  n=todo.pop()
  if n in rows:
   for v in rows[n][1:]:
    if isinstance(v,str) and v not in needed:needed.add(v);todo.append(v)
 e={x:var(x) for x in G['witnesses']+G['fixed_numerals']};e.update(subst or {})
 for n,o,a,b in G['source']:
  if n not in needed:continue
  a=({():a} if a else {}) if type(a)==int else e[a];b=({():b} if b else {}) if type(b)==int else e[b]
  e[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 return e
childres=list(cs.values());p_res=list(ps.values());child=ev(g,childres+['y2','g80','g81'])
parent=ev(par,p_res,{'squareVariable':child['g80'],'ySquareVariable':child['y2']})
assert parent['squareDifference']==parent['ySquareDifference']=={}
common=set(p_res)-{'squareDifference','ySquareDifference','auxResidual'}
assert all(parent[n]==child[n] for n in common)
Q=var('qValueVariable')
assert parent['auxResidual']==add(child['auxResidual'],mul(Q,child['differenceEquality']))
assert child['differenceEquality']==add(add(var('differencePlusOne'),{():1},-1),child['g81'],-1)
assert parent['auxResidual']==add(add(child['y2'],{():1},-1),mul(Q,child['g81']),-1)
unknown=set(g['witnesses']);degree=lambda poly:max((sum(x in unknown for x in m) for m in poly),default=-1)
assert all(degree(child[n])<=2 for n in childres)
for n in childres:
 terms={tuple(x for x in m if x not in unknown):c for m,c in child[n].items() if tuple(x for x in m if x in unknown)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if n=='A0' else {}),(n,terms)
# Explicit positive off-zero counterexample, to distinguish zero equivalence
# from the false universal output identity under the child-to-parent lift.
v={x:1 for x in g['witnesses']};v['differencePlusOne']=2;ports={x:1 for x in g['fixed_numerals']}
pv={x:v[x] for x in par['witnesses'] if x not in {'squareVariable','ySquareVariable'}}
pv.update(squareVariable=v['vValueVariable']**2,ySquareVariable=v['y']**2)
def eval_num(G,values):
 e=dict(values);e.update(ports)
 for n,o,a,b in G['source']:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b;e[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return e[G['output']]
assert (eval_num(par,pv),eval_num(g,v))==(757,759)
assert 'theorem ι_injective' in data['model_ring'] and 'instance' in data['model_ring']
print(json.dumps({'scope':'independent exact residual/DAG and finite inequality illustration; no Lean or model proof',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'positive':{'variables':37,'operations':158,'degree':4,'ops':dict(sorted(ops.items()))},
 'natural':{'variables':37,'operations':195,'degree':4,'ops':dict(sorted(nops.items()))},
 'parent_residuals':29,'child_residuals':28,'exact_parent_aux_equals_child_aux_plus_Q_times_difference':True,
 'off_zero_positive_example':{'all_ports':1,'all_child_inputs':1,'differencePlusOne':2,'parent_output':757,'child_output':759},
 'lean_elaboration':False},sort_keys=True,indent=2))
