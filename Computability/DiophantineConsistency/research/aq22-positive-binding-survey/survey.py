#!/usr/bin/env python3
"""Exact finite survey of AQ22's five plainly positive binding substitutions."""
from itertools import combinations
from collections import Counter
import hashlib,json,sys,time
from pathlib import Path

if not __debug__:raise RuntimeError('assertions required; do not use -O')
D=Path(__file__).resolve().parent
PARENT=D.parent/'adaptive-square-sums22-degree10/candidate.json'
assert hashlib.sha256(PARENT.read_bytes()).hexdigest()=='1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
c=json.loads(PARENT.read_bytes())
vars=c['witnesses']+c['fixed_numerals'];zero=(0,)*len(vars)
residuals=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
# variable -> (defining expression, removable difference)
choices={'scaleVariable':('M','scaleDifference'),'mainScaleVariable':('U','mainScaleDifference'),
         'ellVariable':('ell','ellDifference'),'cSquareVariable':('c2','cSquareDifference'),
         'deltaVariable':('DeltaComputed','deltaDifference')}
rows={r[0]:r for r in c['source']}
assert len(rows)==len(c['source'])==114
# Check that the actual parent output, not just named factors, is their sum of squares.
def square_leaves(name):
 row=rows[name];_,op,a,b=row
 if op=='+' :return square_leaves(a)+square_leaves(b)
 if op=='*' and a==b and a in residuals:return [a]
 raise ValueError(('unexpected parent output wiring',name))
assert Counter(square_leaves(c['output']))==Counter(residuals)
for var,(expression,diff) in choices.items():assert rows[diff]==[diff,'-',var,expression]
class Limit(Exception):pass
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 @staticmethod
 def lift(x):return x if isinstance(x,P) else P({zero:x})
 def __add__(self,x):
  q=self.d.copy()
  for k,v in P.lift(x).d.items():q[k]=q.get(k,0)+v
  return P(q)
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,x):return self+-P.lift(x)
 def __mul__(self,x):
  b=P.lift(x)
  if len(self.d)*len(b.d)>5000000:raise Limit('multiplication pair limit')
  out={}
  for k,a in self.d.items():
   for l,bv in b.d.items():
    m=tuple(i+j for i,j in zip(k,l));out[m]=out.get(m,0)+a*bv
  if len(out)>200000:raise Limit('term limit')
  return P(out)
 def __eq__(self,x):return self.d==P.lift(x).d
base={}
for i,n in enumerate(vars):
 k=list(zero);k[i]=1;base[n]=P({tuple(k):1})
def eval_node(name, replacements, memo, trail=()):
 if isinstance(name,int):return P.lift(name)
 if name in replacements:
  if name in trail:raise ValueError(('cycle',name))
  return eval_node(replacements[name],replacements,memo,trail+(name,))
 if name in memo:return memo[name]
 if name in base:return base[name]
 n,op,a,b=rows[name];x=eval_node(a,replacements,memo,trail+(name,));y=eval_node(b,replacements,memo,trail+(name,))
 if op=='+':z=x+y
 elif op=='-':z=x-y
 elif op=='*':z=x*y
 else:raise ValueError(('operator',op))
 memo[name]=z;return z

def substitute(p,replacements,memo):
 out=P.lift(0)
 for mon,coef in p.d.items():
  term=P.lift(coef)
  for name,e in zip(vars,mon):
   if e:
    v=eval_node(name,replacements,memo)
    for _ in range(e):term=term*v
  out=out+term
 return out

def live_count(factors,replacements):
 live=set(); stack=list(factors)
 while stack:
  name=stack.pop()
  if not isinstance(name,str):continue
  if name in replacements:stack.append(replacements[name]);continue
  if name in live:continue
  live.add(name)
  if name in rows:stack.extend(rows[name][2:])
 return len(live & set(rows)) + len(factors) + max(0,len(factors)-1)

def build_graph(subset):
 repl={name:choices[name][0] for name in subset};removed={choices[name][1] for name in subset}
 factors=[n for n in residuals if n not in removed]
 live=set();stack=list(factors)
 while stack:
  name=stack.pop()
  if not isinstance(name,str):continue
  if name in repl:stack.append(repl[name]);continue
  if name in live:continue
  live.add(name)
  if name in rows:stack.extend(rows[name][2:])
 source=[];available=set(vars)-set(subset)
 for name,op,a,b in c['source']:
  if name not in live:continue
  a=repl.get(a,a);b=repl.get(b,b)
  assert all(isinstance(x,int) or x in available for x in (a,b)),('non-topological',name,a,b)
  source.append([name,op,a,b]);available.add(name)
 squares=[]
 for i,name in enumerate(factors):
  sq='bindingSurveySquare'+str(i);assert sq not in available
  source.append([sq,'*',name,name]);available.add(sq);squares.append(sq)
 acc=squares[0]
 for i,name in enumerate(squares[1:]):
  result='bindingSurveySum'+str(i);assert result not in available
  source.append([result,'+',acc,name]);available.add(result);acc=result
 return {'scope':'Research candidate: exact finite arithmetic checks and ordinary positive witness reconstruction, no new Lean proof.',
         'witnesses':[x for x in c['witnesses'] if x not in subset],
         'fixed_numerals':c['fixed_numerals'],'source':source,'output':acc,
         'residuals':factors,'parent_sha256':hashlib.sha256(PARENT.read_bytes()).hexdigest(),
         'eliminated_bindings':{name:choices[name][0] for name in subset}}

def graph_residuals(graph):
 memo=dict(base)
 for name,op,a,b in graph['source']:
  if name.startswith('bindingSurveySquare') or name.startswith('bindingSurveySum'):continue
  x=P.lift(a) if isinstance(a,int) else memo[a];y=P.lift(b) if isinstance(b,int) else memo[b]
  memo[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return {n:memo[n] for n in graph['residuals']}

def calculate(subset):
 repl={name:choices[name][0] for name in subset};removed={choices[name][1] for name in subset}
 factors=[n for n in residuals if n not in removed];memo={}
 polys={n:eval_node(n,repl,memo) for n in factors}
 graph=build_graph(subset)
 assert len(graph['source'])==live_count(factors,repl) and graph_residuals(graph)==polys
 # Independently expand the original residual first, then substitute into it.
 original={}; parent={n:eval_node(n,{},original) for n in residuals}
 for n in residuals:
  expected=P.lift(0) if n in removed else polys[n]
  assert substitute(parent[n],repl,{})==expected, ('substitution identity',subset,n)
 degrees={n:max((sum(k[:22]) for k in p.d),default=-1) for n,p in polys.items()}
 high=max(degrees.values());leading=[]; beta_leading=[]
 for n,p in polys.items():
  if degrees[n]!=high:continue
  grouped={}
  for k,v in p.d.items():
   if sum(k[:22])==high:
    w=k[:22];ports=k[22:];grouped.setdefault(w,{})[ports]=v
  for w,terms in grouped.items():
   if (all(k[1:]==(0,0,0) for k in terms) and
       (all(v>0 for v in terms.values()) or all(v<0 for v in terms.values()))):
    beta_leading.append({'residual':n,'witness_exponents':list(w),'beta_terms':{str(k[0]):v for k,v in terms.items()}})
   if terms in ({(0,0,0,0):1},{(0,0,0,0):-1}):
    leading.append({'residual':n,'witness_exponents':list(w),'coefficient':next(iter(terms.values()))});break
 return {'eliminated':list(subset),'witnesses':22-len(subset),'residuals':len(factors),'gates':live_count(factors,repl),
         'degree_upper_bound':2*high,'degree_exact_after_arbitrary_port_specialization':2*high if leading else None,
         'degree_witness':leading[0] if leading else None,'degree_exact_if_beta_positive':2*high if beta_leading else None,
         'beta_positive_witness':beta_leading[0] if beta_leading else None,'residual_degrees':degrees,'max_residual_terms':max(len(p.d) for p in polys.values()),
         'substitution_identities':len(residuals)}

# Exhaust the specified 31 nonempty subsets; resource-limit failures are explicitly reported.
results=[]
for size in range(1,len(choices)+1):
 for subset in combinations(choices,size):
  start=time.monotonic()
  try:r=calculate(subset);r['status']='EXACT'
  except Limit as exc:r={'eliminated':list(subset),'status':'RESOURCE_LIMIT','reason':str(exc)}
  results.append(r)
  print(r['status'],','.join(subset),'degree',r.get('degree_exact_if_beta_positive'),'gates',r.get('gates'),flush=True)
# Mutation: substituting 1 instead of ell changes the original ell-binding residual.
assert substitute(eval_node('ellDifference',{},{}),{'ellVariable':'ell'},{})==P.lift(0)
assert substitute(eval_node('ellDifference',{},{}),{'ellVariable':1},{})!=P.lift(0)
# Mutation: changing minus to plus in a removed binding is not the zero polynomial.
assert (eval_node('ellVariable',{'ellVariable':'ell'},{})+eval_node('ell',{'ellVariable':'ell'},{}))!=P.lift(0)
result={'status':'COMPLETE_FINITE_SURVEY','parent_sha256':hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        'positive_binding_choices':choices,'subsets_considered':len(results),'results':results,
        'mutation_controls':['replace ell binding expression by 1','replace subtraction by addition'],
        'scope':'Finite arithmetic survey only; integer positivity witness transport is a separate argument, not Lean verification; resource-limited rows are unresolved.'}
full=build_graph(tuple(choices))
assert len(full['witnesses'])==17 and len(full['source'])==99
(D/'candidate17.json').write_text(json.dumps(full,indent=2)+'\n')
(D/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('COMPLETE_FINITE_SURVEY',len(results),flush=True)
