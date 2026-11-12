#!/usr/bin/env python3
"""Independent exact polynomial and operation review of factored roots; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'parent':('research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523'),
 'child':('research/adaptive-square-sums36-factored-roots/candidate.json','92ec1caec949f4cad0cc3e021becfbbb04a971403a76b282d240addc58d58182'),
 'natural':('research/adaptive-square-sums36-factored-roots/natural-candidate.json','e98cee7d35950544eb668ab20efba26d34792f4b2e74208423a1d9df4022d6f4'),
 'author_receipt':('research/adaptive-square-sums36-factored-roots/result.json','b5688a298d31bcb1815bcfceb33ed2283ddfd397f71b6fc84984218e7182151a'),
 'parent_review':('reviews/adaptive-square-sums36-combined-independent/result.json','4f78edfc16c75a8e690c2cb54ab97f5167ceafebbc5924ea6ed989da6181047a')}
data={}
for n,(p,h) in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;data[n]=b.decode()
par,g,nat=map(json.loads,(data['parent'],data['child'],data['natural']))
assert par['intended_domain']==g['intended_domain']=='positive integers' and nat['intended_domain']=='nonnegative integers'
assert g['witnesses']==par['witnesses'] and len(g['witnesses'])==len(nat['witnesses'])==36
assert g['fixed_numerals']==par['fixed_numerals']==nat['fixed_numerals'] and g['output']==par['output']==nat['output']
remove={'root_scaled','root_sum','ZComputed','zScaled','g58','DstarComputed','dScaled'}
replace={'zDifference':['zDifference','+','firstDeltaMinusY','root_btq3'],'dDifference':['dDifference','-','mainScaledDelta','g59']}
expected=[]
for row in par['source']:
 if row[0] in remove:continue
 if row[0]=='zDifference':expected.extend([['firstDelta','-','firstQuotient','root_inner'],['firstScaledDelta','*','scaleVariable','firstDelta'],['firstDeltaMinusY','-','firstScaledDelta','g33']])
 if row[0]=='dDifference':expected.extend([['mainDelta','-','mainQuotient','offsetVariable'],['mainScaledDelta','*','mainScaleVariable','mainDelta']])
 expected.append(replace.get(row[0],row))
assert expected==g['source'] and len(g['source'])==g['operations']==153
shift=lambda x:'shift_'+x if isinstance(x,str) and x in g['witnesses'] else x
assert nat['witnesses']==['n_'+n for n in g['witnesses']]
assert nat['source']==[['shift_'+n,'+','n_'+n,1] for n in g['witnesses']]+[[n,o,shift(x),shift(y)] for n,o,x,y in g['source']]
assert len(nat['source'])==nat['operations']==189
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
ps=squares(par,pr);cs=squares(g,cr);assert len(ps)==len(cs)==27
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
assert ps==cs
res=list(cs.values());pe=ev(par,res+[par['output']]);ce=ev(g,res+[g['output']])
assert all(pe[n]==ce[n] for n in res) and pe[par['output']]==ce[g['output']]
unknown=set(g['witnesses']);degree=lambda poly:max((sum(x in unknown for x in m) for m in poly),default=-1)
assert degree(ce[g['output']])==4 and ce[g['output']].get(('firstQuotient',)*4)==1
assert all(degree(ce[n])<=2 for n in res)
assert dict(ops)=={'*':67,'+':43,'-':43} and dict(nops)=={'*':67,'+':79,'-':43}
print(json.dumps({'scope':'independent exact full polynomial and DAG check; no Lean or internal theorem',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'positive':{'variables':36,'operations':153,'degree':4,'ops':dict(sorted(ops.items()))},
 'natural':{'variables':36,'operations':189,'degree':4,'ops':dict(sorted(nops.items()))},
 'all_27_residual_polynomials_equal':True,'complete_polynomials_equal':True,
 'expanded_output_monomials':len(ce[g['output']]),'firstQuotient_fourth_coefficient':1,'lean_elaboration':False},sort_keys=True,indent=2))
