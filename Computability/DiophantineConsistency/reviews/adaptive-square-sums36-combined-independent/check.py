#!/usr/bin/env python3
"""Independent exact combined-shift graph and residual audit; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'parent':('research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'),
 'child':('research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523'),
 'natural':('research/adaptive-square-sums36-combined-shift-quartic/natural-candidate.json','8f50ba8c70a4f0eddfb44e9a96e2e776f0622d44924649a22ee7592b5c66655c'),
 'author_receipt':('research/adaptive-square-sums36-combined-shift-quartic/result.json','02813e0ec93140504bbc9f18578acb7c2b3ad1eb12be9767db676196c9c0c7ef'),
 'parent_review':('reviews/adaptive-square-sums37-independent/result.json','58ba07591199a0ce77fa6c6863390e3f7b72894c0f6d564d41cdc3e86567094c'),
 'current_mask':('Lean/DiophantineConsistency/CurrentMaskData2011.lean','8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582'),
 'current_kernel':('Lean/DiophantineConsistency/CurrentKernelData2011.lean','529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c'),
 'current_bounds':('Lean/DiophantineConsistency/CurrentMasks2011.lean','403f35c26ffd2d94e4a29af8c826cfa0874ac8f2281bb673c1347989e7d48cea'),
 'cast_example':('research/ordinary14-natural79-corrected-reflection-overlay/source/Natural82Endpoint.lean.src','2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b')}
data={}
for n,(p,h) in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,(n,hashlib.sha256(b).hexdigest());data[n]=b.decode()
par,g,nat=map(json.loads,(data['parent'],data['child'],data['natural']))
assert par['intended_domain']==g['intended_domain']=='positive integers' and nat['intended_domain']=='nonnegative integers'
assert len(par['witnesses'])==37 and len(g['witnesses'])==len(nat['witnesses'])==36
assert g['witnesses']==['combinedShift' if x=='productVariable' else x for x in par['witnesses'] if x!='gammaProductVariable']
assert par['fixed_numerals']==g['fixed_numerals']==nat['fixed_numerals'] and par['output']==g['output']==nat['output']
old={r[0]:r for r in par['source']};new={r[0]:r for r in g['source']}
remove={'g56','gammaProductDifference','gammaProductConstraint','add_gammaProduct'}
changes={'shift':['shift','-','combinedShift','r0'],
 'productDifference':['combinedEquality','-','combinedShift','combinedComputed'],
 'productConstraint':['combinedConstraint','*','combinedEquality','combinedEquality'],
 'addProduct':['addProduct','+','addCube','combinedConstraint'],
 'add_timeProduct':['add_timeProduct','+','add_offset','timeProductConstraint']}
expected=[]
for row in par['source']:
 if row[0] in remove:continue
 if row[0]=='productDifference':expected.append(['combinedComputed','+','g54','g55'])
 expected.append(changes.get(row[0],row))
assert expected==g['source'] and len(g['source'])==g['operations']==155
assert old['q']==['q','+',1,'qm'] and old['qm']==['qm','*','J','beta']
assert old['g54']==['g54','*','mainScaleVariable','gamma'] and old['g55']==['g55','*','productVariable2','q']
shift=lambda x:'shift_'+x if isinstance(x,str) and x in g['witnesses'] else x
assert nat['witnesses']==['n_'+n for n in g['witnesses']]
assert nat['source']==[['shift_'+n,'+','n_'+n,1] for n in g['witnesses']]+[[n,o,shift(x),shift(y)] for n,o,x,y in g['source']]
assert len(nat['source'])==nat['operations']==191
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
ps=squares(par,pr);cs=squares(g,cr);assert len(ps)==28 and len(cs)==27
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
childres=list(cs.values());parentres=list(ps.values());child=ev(g,childres+['g54','g55','H','combinedComputed'])
parent=ev(par,parentres,{'productVariable':child['g55'],'gammaProductVariable':child['g54']})
assert parent['productDifference']==parent['gammaProductDifference']=={}
common=set(parentres)-{'productDifference','gammaProductDifference','dDifference'}
assert all(parent[n]==child[n] for n in common)
assert parent['dDifference']==add(child['dDifference'],mul(child['H'],child['combinedEquality']))
assert child['combinedEquality']==add(var('combinedShift'),child['combinedComputed'],-1)
unknown=set(g['witnesses']);degree=lambda poly:max((sum(x in unknown for x in m) for m in poly),default=-1)
assert all(degree(child[n])<=2 for n in childres)
for n in childres:
 terms={tuple(x for x in m if x not in unknown):c for m,c in child[n].items() if tuple(x for x in m if x in unknown)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if n=='A0' else {}),(n,terms)
# A positive off-zero point demonstrates that a universal output equality is false.
v={x:1 for x in g['witnesses']};v['combinedShift']=4;ports={x:1 for x in g['fixed_numerals']}
pv={x:v[x] for x in par['witnesses'] if x not in {'productVariable','gammaProductVariable'}}
pv.update(productVariable=v['productVariable2']*(1+v['J']*ports['beta']),gammaProductVariable=v['mainScaleVariable']*v['gamma'])
def num(G,values):
 e=dict(values);e.update(ports)
 for n,o,a,b in G['source']:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b;e[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return e[G['output']]
assert (num(par,pv),num(g,v))==(1361,2209)
assert 1+1*(-1)==0 # negative beta can invalidate the claimed positive lift
assert 'def radix : ℕ := 2 ^ 47' in data['current_mask'] and 'def beta : ℕ := radix ^ 2011 - 1' in data['current_mask']
assert 'def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in data['current_mask']
assert 'theorem beta_pos : 0 < beta' in data['current_bounds'] and 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in data['current_kernel']
assert 'simp only [Int.cast_natCast, map_natCast]' in data['cast_example']
print(json.dumps({'scope':'independent exact source/DAG/residual and beta-interface review; no Lean or model proof',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'positive':{'variables':36,'operations':155,'degree':4,'ops':dict(sorted(ops.items()))},
 'natural':{'variables':36,'operations':191,'degree':4,'ops':dict(sorted(nops.items()))},
 'parent_residuals':28,'child_residuals':27,'parent_d_equals_child_d_plus_H_times_combined':True,
 'off_zero_example':{'parent':1361,'child':2209,'beta':1},
 'negative_beta_can_break_this_lift':True,'model_beta_cast_is_unelaborated':True,'lean_elaboration':False},sort_keys=True,indent=2))
