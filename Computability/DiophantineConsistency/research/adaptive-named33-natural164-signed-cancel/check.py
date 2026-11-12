#!/usr/bin/env python3
"""Exact affine-shift cancellation and natural 33/164/8 DAG checks; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
parraw=pin(D/'research/adaptive-square-sums33/candidate.json','a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735');par=json.loads(parraw)
g=json.loads(pin(P/'candidate.json','b42bb4501265b3dfac592b74d0950b79c322064d3febe38aeec56e741112e121'))
lit=pin(D/'Lean/DiophantineConsistency/AdaptiveNamedValues33.lean','0c6bde076f2cc77e2d4d08f7542abb6bf469b6062e0ab7d1276250da1b06abbb').decode()
endpoint=pin(D/'Lean/DiophantineConsistency/IPRANamedValues33Native.lean','c6c072f16c436d8e4608753684f1afceda523b2789c33ff4c192e5fdb624f8ce').decode()
assert 'positiveShift\n  (AdaptiveNamedValues33.literal CurrentWindowCarry2011.ports)' in endpoint
assert '∼mappedNativeRefutation embedding' in endpoint
start=lit.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n');end=lit.index('\ndef embed ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=']
expected += [f'  let {n} : Expr (Fin 33) := .var ({i})' for i,n in enumerate(par['witnesses'])]
expected += [f'  let {n} : Expr (Fin 33) := .constant (p {i})' for i,n in enumerate(par['fixed_numerals'])]
expected += [f'  let {n} := {a} {o} {b}' for n,o,a,b in par['source']]
expected += ['  '+par['output']]
assert lit[start:end].splitlines()==expected and len(par['source'])==139 and len(par['witnesses'])==33
pairs=[('namedBt','wPositive','wNegative'),('Z','zPositive','zNegative'),('Dstar','dPositive','dNegative'),('V','vPositive','vNegative')]
unshifted={x for _,a,b in pairs for x in (a,b)}
assert len(unshifted)==8
for n,a,b in pairs:
 assert [n,'-',a,b] in par['source']
 for x in (a,b):assert [r[0] for r in par['source'] if x in r[2:]]==[n]
ren={n:'n_'+n for n in par['witnesses']}
def inp(x):
 if not isinstance(x,str) or x not in ren:return x
 return ren[x] if x in unshifted else 'shift_'+x
expected_rows=[['shift_'+n,'+',ren[n],1] for n in par['witnesses'] if n not in unshifted]
expected_rows += [[n,o,inp(a),inp(b)] for n,o,a,b in par['source']]
assert g['parent_sha256']==sha(parraw) and g['witnesses']==[ren[n] for n in par['witnesses']]
assert g['fixed_numerals']==par['fixed_numerals'] and g['source']==expected_rows
assert len(g['source'])==g['operations']==164 and g['output']==par['output']
# All operations, witnesses and ports are topologically ordered and live.
seen=set(g['witnesses']+g['fixed_numerals']);nodes={}
for n,o,a,b in g['source']:
 assert n not in seen and o in ('+','-','*') and all(isinstance(x,int) or x in seen for x in (a,b))
 seen.add(n);nodes[n]=(a,b)
active={g['output']};todo=[g['output']]
while todo:
 n=todo.pop()
 for x in nodes.get(n,()):
  if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
assert set(nodes)<=active and set(g['witnesses'])<=active and set(g['fixed_numerals'])<=active
# Exact sparse polynomial degree check. Fixed ports are formal coefficients.
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 o=dict(a)
 for m,c in b.items():o[m]=o.get(m,0)+s*c
 return {m:c for m,c in o.items() if c}
def mul(a,b):
 o={}
 for x,c in a.items():
  for y,d in b.items():
   m=tuple(sorted(x+y));o[m]=o.get(m,0)+c*d
 return {m:c for m,c in o.items() if c}
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
res=['A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','aDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference'];assert len(res)==20
values=evaluate(g,res);w=set(g['witnesses']);degree=lambda poly:max((sum(x in w for x in mon) for mon in poly),default=-1)
assert max(degree(values[r]) for r in res)==4
mon=('n_ellVariable','n_ellVariable','n_scaleVariable','n_scaleVariable')
assert values['A0'].get(tuple(sorted(mon)))==-1
# Check output is precisely the sum of the listed residual squares.
env={r:var(r) for r in res}
for n,o,a,b in g['source']:
 if n in env:continue
 if isinstance(a,str) and a not in env:continue
 if isinstance(b,str) and b not in env:continue
 a=con(a) if isinstance(a,int) else env[a];b=con(b) if isinstance(b,int) else env[b]
 env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
assert env[g['output']]=={(r,r):1 for r in res}
print(json.dumps({'scope':'exact source rows, four affine cancellation identities, output shape and degree; no Lean',
 'parent_positive_operations':139,'naive_natural_operations':172,'candidate_natural_operations':164,
 'variables':33,'residuals':20,'degree':8,'operation_counts':dict(sorted(Counter(r[1] for r in g['source']).items())),
 'cancelled_pairs':[list(x) for x in pairs],'matched_parent_literal_rows':True,'lean_elaboration':False},sort_keys=True,indent=2))
