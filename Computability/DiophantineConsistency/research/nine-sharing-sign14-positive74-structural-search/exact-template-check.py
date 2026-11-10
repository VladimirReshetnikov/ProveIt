#!/usr/bin/env python3
"""Exact integer-polynomial check of generic local structural templates."""
import hashlib,itertools,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
canonical=(P/'search_canonical.py').read_text();basis=(P/'search_basis.py').read_text()
start='def alternatives(i):';end='\ndef replace(root,old,new):'
assert canonical.split(start,1)[1].split(end,1)[0]==basis.split(start,1)[1].split(end,1)[0], 'rewrite engines differ'
# Load just the definitions before the search; no beam is run.
env={'__file__':str((P/'search_canonical.py').resolve())}
exec(compile(canonical[:canonical.index('assert len(graph(root)) == 74')],str(P/'search_canonical.py'),'exec'),env)
node,alt,table=env['node'],env['alternatives'],env['N']
variables=[f'formal:{x}' for x in 'abcd']
def plus(p,q,sgn=1):
 r=dict(p)
 for m,c in q.items():r[m]=r.get(m,0)+sgn*c
 return {m:c for m,c in r.items() if c}
def mul(p,q):
 r={}
 for a,x in p.items():
  for b,y in q.items():
   m=tuple(sorted(a+b));r[m]=r.get(m,0)+x*y
 return {m:c for m,c in r.items() if c}
def poly(x):
 if isinstance(x,str):return {(x,):1}
 op,a,b=table[x];p,q=poly(a),poly(b)
 return plus(p,q,1) if op=='add' else plus(p,q,-1) if op=='sub' else mul(p,q)
ops=('add','sub','mul');cases=set()
for op,inner,side in itertools.product(ops,ops,range(2)):
 for a,b,c in itertools.product(variables,repeat=3):
  sub=node(inner,a,b);cases.add(node(op,sub,c) if side==0 else node(op,c,sub))
for op in ('add','sub'):
 for a,b,c,d in itertools.product(variables,repeat=4):cases.add(node(op,node('mul',a,b),node('mul',c,d)))
checked=0
for case in sorted(cases):
 expected=poly(case)
 for candidate in alt(case):
  if poly(candidate)!=expected:raise RuntimeError(f'false identity at {case} -> {candidate}')
  checked+=1
assert checked>0
print(json.dumps({'status':'PASS_EXACT_FORMAL_POLYNOMIAL_TEMPLATES','generic_cases':len(cases),'rewrite_instances_checked':checked,'search_canonical_sha256':hashlib.sha256((P/'search_canonical.py').read_bytes()).hexdigest(),'search_basis_sha256':hashlib.sha256((P/'search_basis.py').read_bytes()).hexdigest(),'scope':'Exact integer-polynomial checks on formal indeterminates for generated local rewrite patterns, not completeness of bounded beam search.'},indent=2,sort_keys=True))
