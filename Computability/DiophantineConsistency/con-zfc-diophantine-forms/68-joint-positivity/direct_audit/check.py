#!/usr/bin/env python3
"""Independent literal audit. Reads JSON/source only; imports no submitted code."""
import json, math, itertools, hashlib, re
from collections import defaultdict
from pathlib import Path
D=Path(__file__).resolve().parent; R=D.parent
counts={}
def require(x,msg):
 if not x: raise RuntimeError(msg)
def read(f):return json.loads((R/f).read_text())
def poly(rows):
 d=defaultdict(int)
 for r in rows:d[tuple(sorted(r['monomial']))]+=r['coefficient']
 return {m:c for m,c in d.items() if c}
def add(a,b):
 d=defaultdict(int,a)
 for m,c in b.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def var(s):return {(s,):1}
files=['alternative/branch_scratch_output_independent.json','alternative/horn_output_independent.json']
for f in files:
 o=read(f); degree=0
 require(o['witness_count']==17 and o['common_wire_count']==13,'witness count')
 for b in o['branches']:
  rows=list(map(poly,b['quadratic_residuals'])); total={}
  for p in rows:total=add(total,mul(p,p))
  require(total==poly(b['sum_of_squares']),f+' SOS '+b['name'])
  deg=max(map(len,total));require(deg==b['degree'],'exact factor degree');degree+=deg
  for i,w in enumerate(b['wires']):
   p=poly(w['value']);require(w['name']=='q'+str(i),'wire order')
   require(all(c>=0 for c in p.values()),'constructor positivity')
   require(all(not s.startswith('q') or int(s[1:])<i for mon in p for s in mon),'acyclic wire')
   require(rows[i]==add(var(w['name']),neg(p)),'defining residual exact')
  require(max(map(len,p))<=4 if b['wires'] else True,'wire degree')
 require(degree==o['degree'],'product degree')
 counts[f]={'witnesses':17,'exposed':len(o['exposed']),'degree':degree,'exact_SOS_checks':len(o['branches'])}
h=read(files[1]);a=read('direct/affine_shared_step.json')
require(a['horn_source']==h,'integrated Horn literal source')
require((R/'direct/horn_shared_source.json').read_bytes()==(R/files[1]).read_bytes(),'Horn byte pin')
require(len(a['witnesses'])==len(set(a['witnesses']))==23,'local witnesses unique')
M=add(var('M0'),{():1})
f=lambda x:add({():1},mul(var(x),M))
expected=add(mul(var('Sp'),f('v')),neg(mul(mul(var('S'),f('p')),f('q'))))
require(poly(a['extra_residuals'][0])==expected,'affine update exact')
for p,slack,row in zip(['p','q','v'],['dp','dq','dv'],a['extra_residuals'][1:]):
 require(poly(row)==add(add(var(p),var(slack)),neg(var('m'))),'bound residual')
require(a['exact_degree']==50,'local affine degree')
# Each emitted Lean local let is parsed back to sparse monomials.
lean=(R/'direct/SharedAffineProductEquation.lean').read_text()
lookup={'inl':a['exposed_coordinates'],'inr':a['witnesses']}
lets=re.findall(r'  let ([he]\d+) : .*? := (.*)',lean)
require(len(lets)==16,'Lean local lets')
for key,expression in lets:
 terms=expression.split(' + ');got=defaultdict(int)
 for term in terms:
  c=re.search(r'\.constant \((-?\d+) : ℤ\)',term);require(c is not None,'Lean coefficient')
  mon=tuple(sorted(lookup[k][int(i)] for k,i in re.findall(r'\.var \(\.(in[lr]) (\d+)\)',term)))
  got[mon]+=int(c.group(1));require(term.count('(')==term.count(')'),'balanced local term')
 wanted=h['branches'][int(key[1:])]['sum_of_squares'] if key[0]=='h' else a['extra_residuals'][int(key[1:])]
 require({m:c for m,c in got.items() if c}==poly(wanted),'Lean local literal '+key)
require(lean.count('.boundedForall ')==2,'two bounded blocks')
for s in ['boundedForall (0 : Fin 5)','boundedForall (3 : Fin 5)', '(.var 0 - .var 2 - 2)', '(.var 1 - 1)', '(Sum.inr j : Empty ⊕ Fin 5)']:
 require(s in lean,'global constructor static interface '+s)
counts['affine_local']={'witnesses':23,'exposed':4,'degree':50,'Lean_let_roundtrips':16,'global_compiled':False}
# Exhaustive finite nonnegative-flow sanity check, including the free truth label.
rules=[(c,p)for c in range(3)for k in range(3)for p in itertools.combinations_with_replacement(range(3),k)]
flow=0;certs=0
for rr in itertools.combinations_with_replacement(rules,2):
 derived={0}
 while True:
  nxt=derived|{c for c,p in rr if all(x in derived for x in p)}
  if nxt==derived:break
  derived=nxt
 for mult in itertools.product(range(3),repeat=2):
  balance=[0,0,0]
  for n,(c,pp) in zip(mult,rr):
   balance[c]+=n
   for p in pp:balance[p]-=n
  flow+=1
  if balance[1]>=1 and balance[2]>=0:
   certs+=1;require(1 in derived,'flow counterexample')
counts['flow']={'finite_cases':flow,'dominating_certificates':certs}
gcds=0
for m in range(1,61):
 M=math.lcm(*range(1,m+1))
 for i,j in itertools.combinations(range(1,m+1),2):
  require(math.gcd(1+i*M,1+j*M)==1,'affine coprimality');gcds+=1
counts['coprimality_cases']=gcds
for x,y,z in itertools.product(range(7),repeat=3):
 value=abs((z-x)*(z-y)); require((value>=1)==(z!=x and z!=y),'bundle guard')
counts['guard_cases']=343
paths=files+['direct/affine_shared_step.json','direct/SharedAffineProductEquation.lean']
counts['sha256']={f:hashlib.sha256((R/f).read_bytes()).hexdigest() for f in paths}
# Inherited API/calculus files are pinned data, not a newly compiled closure.
pins=json.loads((D/'inherited/SOURCE_PINS.json').read_text())
for item in pins['files']:
 data=(D/'inherited/sources'/(item['name']+'.lean')).read_bytes()
 require(hashlib.sha256(data).hexdigest()==item['sha256'],'pinned source '+item['name'])
counts['inherited_source_pins']=len(pins['files'])
print(json.dumps({'status':'PASS','checks':counts},indent=2))
