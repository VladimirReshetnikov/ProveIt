#!/usr/bin/env python3
"""Independent exact sparse-polynomial comparison of named33 natural graph."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/adaptive-square-sums33/candidate.json','a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735'))
c=json.loads(pin('research/adaptive-named33-natural164-signed-cancel/candidate.json','b42bb4501265b3dfac592b74d0950b79c322064d3febe38aeec56e741112e121'))
l=pin('Lean/DiophantineConsistency/AdaptiveNamedValues33.lean','0c6bde076f2cc77e2d4d08f7542abb6bf469b6062e0ab7d1276250da1b06abbb').decode()
e=pin('Lean/DiophantineConsistency/IPRANamedValues33Native.lean','c6c072f16c436d8e4608753684f1afceda523b2789c33ff4c192e5fdb624f8ce').decode()
pin('research/adaptive-named33-natural164-signed-cancel/result.json','f49ea7a21afcd85eb46823504f411c33b8a57eec6fc3ed9fd3f91055f6b324ee')
pin('reviews/ipra-named33-native-verification/README.md','b1feb7f467f9c6d1f2a53df27ba49aadef0948c197cb82d563924be5cbd2bfb7')
assert len(p['witnesses'])==len(c['witnesses'])==33 and len(p['source'])==139 and len(c['source'])==164
assert c['witnesses']==['n_'+x for x in p['witnesses']] and p['fixed_numerals']==c['fixed_numerals']
assert 'positiveShift\n  (AdaptiveNamedValues33.literal CurrentWindowCarry2011.ports)' in e and '∼mappedNativeRefutation embedding' in e
pairs=[('namedBt','wPositive','wNegative'),('Z','zPositive','zNegative'),('Dstar','dPositive','dNegative'),('V','vPositive','vNegative')]
for n,a,b in pairs:
 assert [n,'-',a,b] in p['source']
 assert [r[0] for r in p['source'] if a in r[2:]]==[n] and [r[0] for r in p['source'] if b in r[2:]]==[n]
 assert [n,'-','n_'+a,'n_'+b] in c['source']
# All nodes and input symbols participate in the output.
rows={n:(a,b) for n,_,a,b in c['source']}
assert len(rows)==164
active={c['output']};todo=[c['output']]
while todo:
 n=todo.pop()
 for x in rows.get(n,()):
  if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
assert set(rows)|set(c['witnesses'])|set(c['fixed_numerals'])<=active
# Canonical polynomials over all 33 inputs AND 4 arbitrary ports, represented
# by sorted variable tuples. Parent variables are substituted by x+1.
def atom(n):return {(n,):1}
def add(a,b,sign=1):
 d=dict(a)
 for m,k in b.items():d[m]=d.get(m,0)+sign*k
 return {m:k for m,k in d.items() if k}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ka in a.items():
  for mb,kb in b.items():d[tuple(sorted(ma+mb))]+=ka*kb
 return {m:k for m,k in d.items() if k}
def evalgraph(g,shift):
 env={n:(add(atom('n_'+n),{():1}) if shift else atom(n)) for n in g['witnesses']}
 env.update({n:atom(n) for n in g['fixed_numerals']})
 for n,op,a,b in g['source']:
  assert n not in env and op in '+-*'
  a=env[a] if isinstance(a,str) else ({():a} if a else {})
  b=env[b] if isinstance(b,str) else ({():b} if b else {})
  env[n]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 return env
a,b=evalgraph(p,True),evalgraph(c,False)
assert a[p['output']]==b[c['output']]
# Count witness degree after expansion; ports count as symbolic coefficients.
inputs=set(c['witnesses']);degree=lambda m:sum(x in inputs for x in m)
poly=b[c['output']]; assert max(map(degree,poly))==8
# Explicit coefficient of ell⁴ scale⁴ is port-independent and >0;
# hence degree eight persists after specializing ports to arbitrary integers.
target=tuple(sorted(['n_ellVariable']*4+['n_scaleVariable']*4))
assert poly.get(target,0)>0
assert not any(tuple(x for x in m if x in inputs)==target and any(x not in inputs for x in m) for m in poly)
# Bound parent Lean source to identical declaration, all rows and output.
start=l.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n');end=l.index('\ndef embed ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=']+[f'  let {n} : Expr (Fin 33) := .var ({i})' for i,n in enumerate(p['witnesses'])]+[f'  let {n} : Expr (Fin 33) := .constant (p {i})' for i,n in enumerate(p['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in p['source']]+['  '+p['output']]
assert l[start:end].splitlines()==expected
print(json.dumps({'scope':'exact external integer polynomial identity and parent Lean source rows; no Lean build or new endpoint','inputs':33,'positive_parent_operations':139,'natural_candidate_operations':164,'natural_degree_every_port_tuple':8,'degree_witness_coefficient':poly[target],'expanded_terms':len(poly),'affine_signed_pairs_checked':4,'parent_literal_rows_checked':139},sort_keys=True,indent=2))
