#!/usr/bin/env python3
"""Check the speculative absorbed-r DAG and its forward finite samples."""
from pathlib import Path
from hashlib import sha256
import json,random,re,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;P=H.parent/'ordinary12-direct-main-probe/graph-dag.json';G=H/'graph-dag.json';L=H/'Absorb89Graph.lean'
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
need(sha(P)=='82dd1f55f67ef3487509a6d4d31ef085d5d4813c11df43be40570a3293a8b430','parent drift')
need(sha(G)=='280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd','draft drift')
need(sha(L)=='c74d9a6798e29aa77e93cb075983b91f46cb08cd92de4022a0f7fab02d85f4e0','Lean graph drift')
a=json.loads(P.read_text());b=json.loads(G.read_text());need(b['parent_graph_sha256']==sha(P),'parent pin')
expected=[]
for n,op,x,y in a['source']:
 if n=='g32':continue
 if n=='g33':need((op,x,y)==('*','qm','g32'),'old g33 shape');y='folded_g31'
 expected.append([n,op,x,y])
need(expected==b['source'] and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals'],'transformation')
source=L.read_text().split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\nvariable {R : Type*}',1)[0]
pat=re.compile(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',re.M)
def atom(x):return int(x) if x.isdigit() else x
rows=[[n,op,atom(x),atom(y)] for n,x,op,y in pat.findall(source)]
need(rows==b['source'],'Lean rows mismatch')
for i,n in enumerate(b['witnesses']):need(f'  let {n} : Expr (Fin 12) := .var {i}\n' in source,'witness slot')
for i,n in enumerate(b['fixed_numerals']):need(f'  let {n} : Expr (Fin 12) := .constant (p {i})\n' in source,'port slot')
need('  ⟨A0, A1, N, P12⟩' in source,'outputs')
known=set(b['witnesses']+b['fixed_numerals'])|set(range(5));parents={}
for n,op,x,y in rows:
 need(n not in known and x in known and y in known and op in ('+','-','*'),'topology');known.add(n);parents[n]=(x,y)
live=set();todo=[b['output']]
while todo:
 n=todo.pop()
 if n in parents and n not in live:live.add(n);todo.extend(parents[n])
counts={op:sum(r[1]==op for r in rows) for op in ('*','+','-')}
need(len(rows)==len(live)==89 and counts==b['operation_breakdown']=={'*':50,'+':22,'-':17},'live count')
def evaluate(rows,env):
 v=env.copy();v.update({i:i for i in range(5)})
 for n,op,x,y in rows:
  X,Y=v[x],v[y];v[n]=X*Y if op=='*' else X+Y if op=='+' else X-Y
 return v
rng=random.Random(8901)
for _ in range(100):
 old={k:rng.randrange(1,5) for k in a['witnesses']};old.update({k:rng.randrange(0,5) for k in a['fixed_numerals']});new=old.copy();new['r']=old['r']+old['s']
 x=evaluate(a['source'],old);y=evaluate(b['source'],new)
 for n in b['residuals']+[b['output']]:need(x[n]==y[n],'forward sample '+n)
print(json.dumps({'status':'PASS','draft_sha256':sha(G),'parent_sha256':sha(P),'lean_source_sha256':sha(L),
 'rows':len(rows),'live':len(live),'breakdown':counts,'forward_exact_integer_samples':100,
 'scope':'external DAG/liveness and samples; reverse, halt, iPRA remain unproved'},indent=2))
