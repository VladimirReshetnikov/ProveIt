#!/usr/bin/env python3
"""Independent exact sparse-polynomial comparison of AQ34 natural graph."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/adaptive-square-sums34/candidate.json','9c7fdcf0289b0407af4bbb9deaef4d52fd37435c162a8d15199d1ec9902e1f77'))
c=json.loads(pin('research/adaptive-aq34-natural172-signed-cancel/candidate.json','2bc8d1be1d3e4ca72dd84255816bda819bd75423447c6799c3aa52b8583d8f23'))
l=pin('Lean/DiophantineConsistency/AdaptiveAQ34Literal.lean','30e3a0e4bc8199bcb62d27bcc0cc6a73697027f9c0066d24cbaad340eb2df38b').decode()
e=pin('Lean/DiophantineConsistency/IPRAAQ34Native.lean','857f4eb24f59efabfb49b9e6ba038bc43d1ffd81af70b21827f4b68153f5a31d').decode()
pin('research/adaptive-aq34-natural172-signed-cancel/result.json','fa871961bfe4a62ed1653e539c30e2b0d8a3ad62942051a6d0362479564c4a41')
pin('reviews/adaptive-aq34-native-replay/README.md','0a22d7acda1bcde318f602832f39b96fc140e34e433f990bf5f66203df51bc6f')
assert len(p['witnesses'])==len(c['witnesses'])==34 and len(p['source'])==144 and len(c['source'])==172
assert c['witnesses']==['n_'+x for x in p['witnesses']] and p['fixed_numerals']==c['fixed_numerals']
assert 'positiveShift\n  (AdaptiveAQ34Literal.literal CurrentWindowCarry2011.ports)' in e and '∼mappedNativeRefutation embedding' in e
pairs=[('namedBt','wPositive','wNegative'),('Dstar','dPositive','dNegative'),('V','vPositive','vNegative')]
for n,a,b in pairs:
 assert [n,'-',a,b] in p['source']
 assert [r[0] for r in p['source'] if a in r[2:]]==[n] and [r[0] for r in p['source'] if b in r[2:]]==[n]
 assert [n,'-','n_'+a,'n_'+b] in c['source']
# All nodes and input symbols participate in the output.
rows={n:(a,b) for n,_,a,b in c['source']}
assert len(rows)==172
active={c['output']};todo=[c['output']]
while todo:
 n=todo.pop()
 for x in rows.get(n,()):
  if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
assert set(rows)|set(c['witnesses'])|set(c['fixed_numerals'])<=active
# Canonical polynomials over all 34 inputs AND 4 arbitrary ports, represented
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
poly=b[c['output']]; assert max(map(degree,poly))==6
# Explicit coefficient of ellProduct² scale⁴ is port-independent and >0;
# hence degree six persists after specializing ports to arbitrary integers.
target=tuple(sorted(['n_ellProductVariable']*2+['n_scaleVariable']*4))
assert poly.get(target,0)>0
assert not any(tuple(x for x in m if x in inputs)==target and any(x not in inputs for x in m) for m in poly)
# Bound parent Lean source to identical declaration, all rows and output.
start=l.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 34) :=\n');end=l.index('\ntheorem new_literal ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 34) :=']+[f'  let {n} : Expr (Fin 34) := .var {i}' for i,n in enumerate(p['witnesses'])]+[f'  let {n} : Expr (Fin 34) := .constant (p {i})' for i,n in enumerate(p['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in p['source']]+['  '+p['output']]
assert l[start:end].splitlines()==expected
print(json.dumps({'scope':'exact external integer polynomial identity and parent Lean source rows; no Lean build or new endpoint','inputs':34,'positive_parent_operations':144,'natural_candidate_operations':172,'natural_degree_every_port_tuple':6,'degree_witness_coefficient':poly[target],'expanded_terms':len(poly),'affine_signed_pairs_checked':3,'parent_literal_rows_checked':144},sort_keys=True,indent=2))
