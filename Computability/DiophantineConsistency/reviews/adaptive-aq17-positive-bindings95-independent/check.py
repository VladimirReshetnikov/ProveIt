#!/usr/bin/env python3
"""Full external polynomial equality and exact fixed-port degree for AQ17."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
c=json.loads(pin('research/adaptive-aq17-positive-bindings95/candidate.json','624cc7848f1f36db2d35f5fdfc37111e36ab8e3e8c0ee71553c4fda6739de4fc'))
n=json.loads(pin('research/adaptive-aq17-positive-bindings95/natural-candidate.json','6c454d2bb25bc2226ffc0b23cebd5ea7aa271e3002f3c476ca16a568db7e6b59'))
pin('research/adaptive-aq17-positive-bindings95/receipt.json','c649d2850658912cd0f88265fa20c190c1e06ec31fadb3ee0544973fc458943c')
pin('reviews/adaptive-aq20-substituted-scales104-independent/result.json','b1afbc50dc3a450be310cee4f102f1e0796aaf38c20d107ea5924aff3902901a')
assert len(p['witnesses'])==20 and len(c['witnesses'])==len(n['witnesses'])==17 and len(p['source'])==104 and len(c['source'])==95 and len(n['source'])==112
assert c['witnesses']==[x for x in p['witnesses'] if x not in ('ellVariable','cSquareVariable','deltaVariable')]
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values()) and n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,op,rep(a),rep(b)] for x,op,a,b in c['source']]
assert n['fixed_numerals']==c['fixed_numerals'] and n['output']==c['output']
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
def run(g,subs):
 env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};env.update(subs);rows={}
 for name,op,a,b in g['source']:
  assert name not in env and op in '+-*';rows[name]=(a,b)
  a=env[a] if isinstance(a,str) else ({():a} if a else {})
  b=env[b] if isinstance(b,str) else ({():b} if b else {})
  env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 active={g['output']};todo=[g['output']]
 while todo:
  for x in rows.get(todo.pop(),()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(rows)|set(g['witnesses'])|set(g['fixed_numerals'])<=active
 return env
b=run(c,{})
E=mul(atom('X'),atom('Y'));k=add(atom('eta'),atom('zeta'));cc=add(atom('eta'),mul(atom('Y'),k));aa=add(E,atom('Y'))
ell=mul(mul(E,atom('Y')),k);c2=mul(cc,cc);delta=add(add({():3},mul({():4},aa)),mul(aa,aa))
assert b['ell']==ell and b['c2']==c2 and b['DeltaComputed']==delta
a=run(p,{'ellVariable':ell,'cSquareVariable':c2,'deltaVariable':delta})
assert a[p['output']]==b[c['output']]
assert all(not a[x] for x in ['ellDifference','cSquareDifference','deltaDifference'])
inputs=set(c['witnesses']);out=b[c['output']];degree=lambda mon:sum(x in inputs for x in mon)
assert max(map(degree,out))==20
witness=tuple(sorted(['Y']*8+['eta']*8+['i']*4))
coeff={tuple(x for x in mon if x not in inputs):v for mon,v in out.items() if tuple(x for x in mon if x in inputs)==witness}
assert coeff=={():1},coeff
print(json.dumps({'scope':'full symbolic output equality and positive binding analysis; no Lean','positive_variables':17,'positive_operations':95,'natural_operations':112,'output_terms':len(out),'degree_at_every_integer_port_tuple':20,'degree20_port_independent_witness_coefficient':1,'three_bindings_zero_after_substitution':True,'new_model_transport_not_elaborated':True},sort_keys=True,indent=2))
