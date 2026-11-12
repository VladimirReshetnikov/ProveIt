#!/usr/bin/env python3
"""Exact distributive root-binding identities, DAG/degree certificates; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
parentraw=pin(D/'research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523');parent=json.loads(parentraw)
childraw=pin(P/'candidate.json','92ec1caec949f4cad0cc3e021becfbbb04a971403a76b282d240addc58d58182');child=json.loads(childraw)
nat=json.loads(pin(P/'natural-candidate.json','e98cee7d35950544eb668ab20efba26d34792f4b2e74208423a1d9df4022d6f4'))
assert child['parent_sha256']==sha(parentraw) and nat['positive_parent_sha256']==sha(childraw)
remove={'root_scaled','root_sum','ZComputed','zScaled','g58','DstarComputed','dScaled'}
replace={'zDifference':['zDifference','+','firstDeltaMinusY','root_btq3'], 'dDifference':['dDifference','-','mainScaledDelta','g59']}
rows=[]
for r in parent['source']:
 if r[0] in remove:continue
 if r[0]=='zDifference':rows.extend([['firstDelta','-','firstQuotient','root_inner'],['firstScaledDelta','*','scaleVariable','firstDelta'],['firstDeltaMinusY','-','firstScaledDelta','g33']])
 if r[0]=='dDifference':rows.extend([['mainDelta','-','mainQuotient','offsetVariable'],['mainScaledDelta','*','mainScaleVariable','mainDelta']])
 rows.append(replace.get(r[0],r))
assert child['source']==rows and len(rows)==child['operations']==153
assert child['witnesses']==parent['witnesses'] and len(child['witnesses'])==36
assert child['fixed_numerals']==parent['fixed_numerals'] and child['output']==parent['output']
ren={n:'n_'+n for n in child['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert nat['witnesses']==[ren[x] for x in child['witnesses']]
assert nat['source']==[['shift_'+n,'+',ren[n],1] for n in child['witnesses']]+[[n,o,rep(a),rep(b)] for n,o,a,b in child['source']]
assert nat['operations']==len(nat['source'])==189 and nat['output']==child['output'] and nat['fixed_numerals']==child['fixed_numerals']
def live(G):
 seen=set(G['witnesses']+G['fixed_numerals']);nodes={}
 for n,o,a,b in G['source']:
  assert n not in seen and o in ('+','-','*') and all(isinstance(x,int) or x in seen for x in (a,b))
  seen.add(n);nodes[n]=(a,b)
 active={G['output']};todo=[G['output']]
 while todo:
  n=todo.pop()
  for x in nodes.get(n,()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(nodes)<=active and set(G['witnesses'])<=active and set(G['fixed_numerals'])<=active
 return dict(sorted(Counter(r[1] for r in G['source']).items()))
posops=live(child);natops=live(nat)
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   m=tuple(sorted(x+y));out[m]=out.get(m,0)+a0*b0
 return {m:c for m,c in out.items() if c}
def evaluate(G,targets):
 rows={n:(o,a,b) for n,o,a,b in G['source']};need=set(targets);todo=list(targets)
 while todo:
  n=todo.pop()
  if n in rows:
   for x in rows[n][1:]:
    if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
 env={x:var(x) for x in G['witnesses']+G['fixed_numerals']}
 for n,o,a,b in G['source']:
  if n not in need:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 return env
res=['A0','A1','auxResidual','g72','differenceEquality','scaleDifference','mainScaleDifference','rankDifference','ellDifference','wDifference','cubeDifference','combinedEquality','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','scaledIndexDifference','qSignedDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','timeProductDifference']
assert len(res)==27
p=evaluate(parent,res);c=evaluate(child,res)
assert all(p[r]==c[r] for r in res)
def square_sum_shape(G,res):
 env={r:var(r) for r in res}
 for n,o,a,b in G['source']:
  if n in env:continue
  if isinstance(a,str) and a not in env:continue
  if isinstance(b,str) and b not in env:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 assert env[G['output']]=={(r,r):1 for r in res}
square_sum_shape(parent,res);square_sum_shape(child,res)
w=set(child['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
assert all(degree(c[r])<=2 for r in res)
for r in res:
 terms={tuple(x for x in mon if x not in w):coef for mon,coef in c[r].items() if tuple(x for x in mon if x in w)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if r=='A0' else {}),(r,terms)
print(json.dumps({'scope':'exact all-port distributive polynomial equality, source/DAG and degree evidence; no Lean',
 'parent_positive':{'variables':36,'operations':155,'residuals':27,'degree':4},
 'candidate_positive':{'variables':36,'operations':153,'residuals':27,'degree':4,'operations_by_kind':posops},
 'candidate_natural_shift':{'variables':36,'operations':189,'degree':4,'operations_by_kind':natops},
 'all_27_residuals_identical':True,'complete_output_polynomial_identical':True,
 'firstQuotient_fourth_coefficient':1,'lean_elaboration':False},sort_keys=True,indent=2))
