#!/usr/bin/env python3
"""Exact combined-shift residuals, degree, graph and port checks; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
parraw=pin(D/'research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea');par=json.loads(parraw)
childraw=pin(P/'candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523');g=json.loads(childraw)
nat=json.loads(pin(P/'natural-candidate.json','8f50ba8c70a4f0eddfb44e9a96e2e776f0622d44924649a22ee7592b5c66655c'))
mask=pin(D/'Lean/DiophantineConsistency/CurrentMaskData2011.lean','8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582').decode()
pos=pin(D/'Lean/DiophantineConsistency/CurrentMasks2011.lean','403f35c26ffd2d94e4a29af8c826cfa0874ac8f2281bb673c1347989e7d48cea').decode()
ports=pin(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean','529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c').decode()
for x in ('def radix : ℕ := 2 ^ 47','def beta : ℕ := radix ^ 2011 - 1','def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]'):assert x in mask
assert 'theorem beta_pos : 0 < beta' in pos and 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in ports
assert g['parent_sha256']==sha(parraw) and nat['positive_parent_sha256']==sha(childraw)
remove={'g56','gammaProductDifference','gammaProductConstraint','add_gammaProduct'}
replace={'shift':['shift','-','combinedShift','r0'],
 'productDifference':['combinedEquality','-','combinedShift','combinedComputed'],
 'productConstraint':['combinedConstraint','*','combinedEquality','combinedEquality'],
 'addProduct':['addProduct','+','addCube','combinedConstraint'],
 'add_timeProduct':['add_timeProduct','+','add_offset','timeProductConstraint']}
rows=[]
for r in par['source']:
 if r[0] in remove:continue
 if r[0]=='productDifference':rows.append(['combinedComputed','+','g54','g55'])
 rows.append(replace.get(r[0],r))
assert g['source']==rows and len(rows)==g['operations']==155
assert g['witnesses']==[('combinedShift' if x=='productVariable' else x) for x in par['witnesses'] if x!='gammaProductVariable']
assert len(g['witnesses'])==36 and g['fixed_numerals']==par['fixed_numerals'] and g['output']==par['output']
oldrows={r[0]:r for r in par['source']}
for name,row in {'qm':['qm','*','J','beta'],'q':['q','+',1,'qm'],
 'g54':['g54','*','mainScaleVariable','gamma'],'g55':['g55','*','productVariable2','q'],
 'g56':['g56','+','gammaProductVariable','productVariable'],
 'productDifference':['productDifference','-','productVariable','g55'],
 'gammaProductDifference':['gammaProductDifference','-','gammaProductVariable','g54']}.items():assert oldrows[name]==row
ren={n:'n_'+n for n in g['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert nat['witnesses']==[ren[x] for x in g['witnesses']]
assert nat['source']==[['shift_'+n,'+',ren[n],1] for n in g['witnesses']]+[[n,o,rep(a),rep(b)] for n,o,a,b in g['source']]
assert len(nat['source'])==nat['operations']==191 and nat['output']==g['output'] and nat['fixed_numerals']==g['fixed_numerals']
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
parentres=['A0','A1','auxResidual','g72','differenceEquality','scaleDifference','mainScaleDifference','rankDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference','qSquareDifference','product2Difference','scaledIndexDifference','qSignedDifference','rankSeedDifference','ySumDifference','rootSkewDifference','offsetDifference','gammaProductDifference','timeProductDifference']
removedres={'productDifference','gammaProductDifference'};common=[r for r in parentres if r not in removedres];childres=common+['combinedEquality']
assert len(parentres)==28 and len(childres)==27
child=evaluate(g,childres+['g54','g55','H','combinedComputed'])
parent=evaluate(par,parentres,{'productVariable':child['g55'],'gammaProductVariable':child['g54']})
assert parent['productDifference']==parent['gammaProductDifference']=={}
assert all(parent[r]==child[r] for r in common if r!='dDifference')
assert parent['dDifference']==add(child['dDifference'],mul(child['H'],child['combinedEquality']))
assert child['combinedEquality']==add(var('combinedShift'),child['combinedComputed'],-1)
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
print(json.dumps({'scope':'exact graph, source port and conditional residual identities; model reasoning and Lean not executed',
 'parent_positive':{'variables':37,'operations':158,'residuals':28,'degree':4},
 'candidate_positive':{'variables':36,'operations':155,'residuals':27,'degree':4,'operations_by_kind':posops},
 'candidate_natural_shift':{'variables':36,'operations':191,'degree':4,'operations_by_kind':natops},
 'reconstructed_parent_variables':['productVariable=productVariable2*(1+J*beta)','gammaProductVariable=mainScaleVariable*gamma'],
 'parent_d_equals_child_d_plus_H_times_combined_residual':True,'firstQuotient_fourth_coefficient':1,
 'fixed_current_beta_source_positive':True,'lean_elaboration':False},sort_keys=True,indent=2))
