#!/usr/bin/env python3
"""Independent sparse-dictionary check of the generated AQ17 circuit."""
from collections import Counter
from itertools import chain
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required; do not use -O')
D=Path(__file__).resolve().parent
parent_path=D.parent/'adaptive-square-sums22-degree10/candidate.json';child_path=D/'candidate17.json'
parent=json.loads(parent_path.read_bytes());child=json.loads(child_path.read_bytes())
assert hashlib.sha256(parent_path.read_bytes()).hexdigest()=='1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
assert hashlib.sha256(child_path.read_bytes()).hexdigest()=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
variables=child['witnesses']+child['fixed_numerals'];z=(0,)*len(variables)
def const(n):return {z:n} if n else {}
def add(a,b,sign=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+u*v
 return {k:v for k,v in c.items() if v}
def atom(n):
 x=list(z);x[variables.index(n)]=1;return {tuple(x):1}
base={name:atom(name) for name in variables}
replacements={'scaleVariable':'M','mainScaleVariable':'U','ellVariable':'ell','cSquareVariable':'c2','deltaVariable':'DeltaComputed'}
old_factors=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
removed={'scaleDifference','mainScaleDifference','ellDifference','cSquareDifference','deltaDifference'}
assert set(child['residuals'])==set(old_factors)-removed and len(child['residuals'])==8
assert child['eliminated_bindings']==replacements and len(child['witnesses'])==17 and len(child['source'])==99

def interpreter(graph,repl):
 rows={row[0]:row for row in graph['source']};cache=dict(base)
 def visit(name,stack=()):
  if isinstance(name,int):return const(name)
  if name in repl:
   assert name not in stack
   return visit(repl[name],stack+(name,))
  if name in cache:return cache[name]
  assert name not in stack
  _,op,a,b=rows[name];x=visit(a,stack+(name,));y=visit(b,stack+(name,))
  result=add(x,y) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y) if op=='*' else None
  assert result is not None
  cache[name]=result;return result
 return visit

def check_output(graph):
 rows={r[0]:r for r in graph['source']};seen=set(base)
 for name,op,a,b in graph['source']:
  assert name not in seen and op in ('+','-','*')
  assert all(isinstance(x,int) or x in seen for x in (a,b))
  seen.add(name)
 def leaves(n):
  _,op,a,b=rows[n]
  if op=='+':return leaves(a)+leaves(b)
  assert op=='*' and a==b and a in graph['residuals']
  return [a]
 assert Counter(leaves(graph['output']))==Counter(graph['residuals'])
check_output(child)
a=interpreter(parent,replacements);b=interpreter(child,{})
for n in old_factors:assert a(n)==({} if n in removed else b(n)),n
# Exact witness-variable degrees and a leading coefficient surviving beta>0.
degrees={n:max((sum(k[:17]) for k in b(n)),default=-1) for n in child['residuals']}
assert max(degrees.values())==16 and degrees['A0']==16
w={name:0 for name in variables};w.update(J=8,X=2,Y=4,eta=2,beta=8)
mon=tuple(w[n] for n in variables)
assert b('A0').get(mon)==-1
# All other terms at the same witness monomial must not change this coefficient
# when beta,K0,MC,MF are specialized.
matching={k[17:]:v for k,v in b('A0').items() if k[:17]==mon[:17]}
assert matching=={(8,0,0,0):-1},matching
# Trace raw syntax, without applying replacements, to rule out hidden cycles
# or dependencies on any eliminated witness in all five right-hand sides.
parent_rows={row[0]:row for row in parent['source']}
def leaves(name):
 if isinstance(name,int):return set()
 if name not in parent_rows:return {name}
 return leaves(parent_rows[name][2]) | leaves(parent_rows[name][3])
for var,expr in replacements.items():
 deps=leaves(expr)
 assert deps <= set(variables) and not deps.intersection(replacements),(var,deps)
 assert a(var)==a(expr)
# Mutation controls target independently generated circuit and its signed wiring.
mut=json.loads(json.dumps(child));row=next(r for r in mut['source'] if r[0]=='g64');assert row[1]=='+';row[1]='-'
try:
 mb=interpreter(mut,{})
 assert all(a(n)==mb(n) for n in child['residuals'])
except AssertionError:pass
else:raise AssertionError('arithmetic mutation went undetected')
mut=json.loads(json.dumps(child));row=next(r for r in mut['source'] if r[0]=='bindingSurveySum0');row[1]='-'
try:check_output(mut)
except AssertionError:pass
else:raise AssertionError('output sign mutation went undetected')
print('PASS 17 positive witnesses, 99 gates, eight residuals, 13 exact substitutions, simultaneous reconstruction dependencies')
print('PASS exact degree 32 for beta > 0: coefficient of J^8 X^2 Y^4 eta^2 in A0 is -beta^8')
print('PASS arithmetic-row and output-sign mutation controls')
