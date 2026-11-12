#!/usr/bin/env python3
"""Exact residual, degree, graph and witness-map identities; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
parraw=pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56');par=json.loads(parraw)
childraw=pin(P/'candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea');g=json.loads(childraw)
nat=json.loads(pin(P/'natural-candidate.json','a6660fea4eb44a9cf2aeed92b7a16bd0b76af5410a275feaceb0661f82509c1a'))
assert g['parent_sha256']==sha(parraw) and nat['positive_parent_sha256']==sha(childraw)
removed={'ySquareDifference','ySquareConstraint','add_ySquare'}
replace={'g81':['g81','-','y2','g80'], 'g82':['g82','*','qValueVariable','diffMinusOne'], 'Fa':['Fa','-','y2','g82'],
 'squareDifference':['differenceEquality','-','diffMinusOne','g81'], 'squareConstraint':['differenceConstraint','*','differenceEquality','differenceEquality'],
 'sumWithConstraint':['sumWithConstraint','+','sumSquares','differenceConstraint'], 'add_qSigned':['add_qSigned','+','add_scaledIndex','qSignedConstraint']}
rows=[]
for r in par['source']:
 if r[0] in removed:continue
 if r[0]=='g82':rows.append(['diffMinusOne','-','differencePlusOne',1])
 rows.append(replace.get(r[0],r))
assert g['source']==rows and len(rows)==g['operations']==158
assert g['witnesses']==[('differencePlusOne' if x=='squareVariable' else x) for x in par['witnesses'] if x!='ySquareVariable']
assert len(g['witnesses'])==37 and g['fixed_numerals']==par['fixed_numerals'] and g['output']==par['output']
ren={n:'n_'+n for n in g['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert nat['witnesses']==[ren[x] for x in g['witnesses']]
assert nat['source']==[['shift_'+n,'+',ren[n],1] for n in g['witnesses']]+[[n,o,rep(a),rep(b)] for n,o,a,b in g['source']]
assert len(nat['source'])==nat['operations']==195 and nat['output']==g['output'] and nat['fixed_numerals']==g['fixed_numerals']
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
posops=live(g);natops=live(nat)
# Exact sparse polynomials over witness and four formal port indeterminates.
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
def evaluate(G,targets,sub=None):
 rows={n:(o,a,b) for n,o,a,b in G['source']};need=set(targets);todo=list(targets)
 while todo:
  n=todo.pop()
  if n in rows:
   for x in rows[n][1:]:
    if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
 env={x:var(x) for x in G['witnesses']+G['fixed_numerals']};env.update(sub or {})
 for n,o,a,b in G['source']:
  if n not in need:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 return env
parentres=['A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','scaledIndexDifference','ySquareDifference','qSignedDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','gammaProductDifference','timeProductDifference']
removedres={'squareDifference','ySquareDifference'};common=[r for r in parentres if r not in removedres];childres=common+['differenceEquality']
assert len(parentres)==29 and len(childres)==28
child=evaluate(g,childres+['y2','g80','g81'])
parent=evaluate(par,parentres,{'squareVariable':child['g80'],'ySquareVariable':child['y2']})
assert parent['squareDifference']==parent['ySquareDifference']=={}
assert all(parent[r]==child[r] for r in common if r!='auxResidual')
assert parent['auxResidual']==add(child['auxResidual'],mul(var('qValueVariable'),child['differenceEquality']))
assert child['differenceEquality']==add(add(var('differencePlusOne'),con(1),-1),child['g81'],-1)
# At a parent zero: Q*(y²-v²)=y²-1; Q>0 and y>=1 force the difference >=0.
assert parent['auxResidual']==add(add(child['y2'],con(1),-1),mul(var('qValueVariable'),child['g81']),-1)
def square_sum_shape(G,res):
 env={r:var(r) for r in res}
 for n,o,a,b in G['source']:
  if n in env:continue
  if isinstance(a,str) and a not in env:continue
  if isinstance(b,str) and b not in env:continue
  a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 assert env[G['output']]=={(r,r):1 for r in res}
square_sum_shape(par,parentres);square_sum_shape(g,childres)
w=set(g['witnesses']);degree=lambda p:max((sum(x in w for x in mon) for mon in p),default=-1)
assert all(degree(child[r])<=2 for r in childres)
for r in childres:
 terms={tuple(x for x in mon if x not in w):c for mon,c in child[r].items() if tuple(x for x in mon if x in w)==('firstQuotient','firstQuotient')}
 assert terms==({():1} if r=='A0' else {}),(r,terms)
print(json.dumps({'scope':'exact graph and conditional residual identities; model reasoning and Lean not executed',
 'parent_positive':{'variables':38,'operations':160,'residuals':29,'degree':4},
 'candidate_positive':{'variables':37,'operations':158,'residuals':28,'degree':4,'operations_by_kind':posops},
 'candidate_natural_shift':{'variables':37,'operations':195,'degree':4,'operations_by_kind':natops},
 'reconstructed_parent_variables':['squareVariable=vValueVariable²','ySquareVariable=y²'],
 'parent_aux_equals_child_aux_plus_Q_times_difference_residual':True,'firstQuotient_fourth_coefficient':1,
 'lean_elaboration':False},sort_keys=True,indent=2))
