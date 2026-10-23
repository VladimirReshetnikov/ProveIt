"""Independent exact local-data audit. Executes no generator or upstream code."""
import json,hashlib,re
from pathlib import Path
from collections import defaultdict
D=Path(__file__).resolve().parents[1]/'direct'
def need(b,msg):
 if not b: raise ValueError(msg)
def add(a,b,s=1):
 c=dict(a)
 for k,v in b.items(): c[k]=c.get(k,0)+s*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for x,v in a.items():
  for y,w in b.items(): c[tuple(sorted(x+y))]+=v*w
 return {k:v for k,v in c.items() if v}
def aff(a): return {(k,) if k else ():v for k,v in a.items() if v}
def sparse(a):
 p={tuple(x['monomial']):x['coefficient'] for x in a}
 need(len(p)==len(a),'duplicate monomial')
 need(all(type(v)==int and v and tuple(sorted(k))==k for k,v in p.items()),'invalid integer sparse polynomial')
 return p
pins=json.loads((D/'SOURCE_PINS.json').read_text())
for x in pins['files']:
 b=(D/'sources'/(x['name']+'.lean')).read_bytes()
 need(len(b)==x['bytes'],'source length')
 need(hashlib.sha256(b).hexdigest()==x['sha256'],'source sha256')
 need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha'],'source blob')
g=json.loads((D/'stack_step.json').read_text()); q=json.loads((D/'stack_step_quartic.json').read_text())
wire={x['dag_node']:x for x in q['wire_witnesses']}; state=[]; degree=[]
res=[]; reasons=defaultdict(int)
for i,n in enumerate(g['nodes']):
 op=n['op']; args=n['args']
 if op=='const': p={():args[0]}; deg=0
 elif op=='var': p={(args[0],):1}; deg=1
 else:
  need(all(type(j)==int and 0<=j<i for j in args),'topology')
  a,b=[state[j] for j in args]; da,db=[degree[j] for j in args]
  deg=da+db if op=='mul' else max(da,db)
  p=mul(a,b) if op=='mul' else add(a,b,1 if op=='add' else -1)
  if i in wire:
   w=wire[i];need(op=='mul','wire is not product')
   need(a==aff(w['left']) and b==aff(w['right']),'wire input differs from DAG')
   reason=w['nonnegative_reason']; reasons[reason]+=1
   need((a==b) if reason=='square' else all(v>=0 for v in a.values()) and all(v>=0 for v in b.values()),'positivity')
   z={(w['name'],):1};res.append(add(z,p,-1));p=z
 need(max(map(len,p),default=0)<=1,'nonaffine expression without wire')
 state.append(p);degree.append(deg)
res.append(state[g['output']]);need(res==[sparse(x) for x in q['quadratic_residuals']],'residual mismatch')
Q={}
for r in res: Q=add(Q,mul(r,r))
need(Q==sparse(q['quartic_sum_of_squares']),'expanded quartic mismatch')
need((len(wire),len(res),len(Q),max(map(len,Q)))==(84,85,3108,4),'counts')
need(q['witness_count']==89,'witness count')
need(sum(n['op'] in ['add','sub','mul'] for n in g['nodes'])==382,'operations')
need(degree[g['output']]==1048802,'degree')
# Independently parse generated Lean polynomial rows as sums of coefficient-times-monomial.
lean=(D/'OneStackEquation.lean').read_text(); names=['a','b','c','u','v']+[f'q{i}' for i in range(84)]
rows=re.findall(r'  let r(\d+) : Expr .*? := (.*)',lean)
need(len(rows)==85,'Lean row count')
for ix,text in rows:
 parsed={}
 for term in text.split(' + '):
  cs=re.findall(r'\.constant \((-?\d+) : ℤ\)',term)
  vs=re.findall(r'\.var \(\.in([lr]) (\d+)\)',term)
  need(len(cs)<=1,'multiple coefficients')
  m=tuple(sorted((['S','Sp'][int(v)] if side=='l' else names[int(v)]) for side,v in vs))
  coef=int(cs[0]) if cs else 1
  parsed=add(parsed,{m:coef})
 need(parsed==res[int(ix)],'Lean row mismatch '+ix)
need(lean.count('(')==lean.count(')'),'Lean parentheses')
need('sorry' not in lean and '\naxiom ' not in lean,'proof placeholder')
# List coding: exact injectivity on a finite square and strict tail descent.
codes=set()
for h in range(30):
 for t in range(30):
  c=1+(h+t)*(h+t+1)//2+t
  need(c not in codes and t<c,'Cantor list')
  codes.add(c);need(2*c-2-(h+t)*(h+t+1)-2*t==0,'L identity')
receipt={'status':'PASS','source_blobs':len(pins['files']),'DAG_operations':382,'DAG_degree_bound':degree[g['output']], 'local_natural_witnesses':89,'local_total_variables':91,'quadratic_residuals':85,'quartic_monomials':3108,'quartic_degree':4,'positivity_reasons':dict(reasons),'Lean_literal_rows_checked':85,'list_fixture_pairs':900,'Lean_compiled':False,'global_polynomial_materialized':False}
print(json.dumps(receipt,indent=2))
