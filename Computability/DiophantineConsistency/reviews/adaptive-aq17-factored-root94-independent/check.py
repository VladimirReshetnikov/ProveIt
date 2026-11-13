#!/usr/bin/env python3
"""Independent full-output all-port equality for factored-root graph."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-aq17-positive-bindings95/candidate.json','624cc7848f1f36db2d35f5fdfc37111e36ab8e3e8c0ee71553c4fda6739de4fc'))
c=json.loads(pin('research/adaptive-aq17-factored-root94/candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'))
n=json.loads(pin('research/adaptive-aq17-factored-root94/natural-candidate.json','30571052ff20a5fac63f6ab1cfb25292e5bdde42972433b21aaa9be5e9b030c2'))
pin('research/adaptive-aq17-factored-root94/receipt.json','9cdd2dbd3fc2ccdf64c7eeee0f952dae0e73bfb05adccd8dadab600a91625106')
pin('reviews/adaptive-aq17-positive-bindings95-independent/result.json','442620a36b18ca9530629d060de300478a1fdd1242a0f58eff2583592dfa4a75')
assert len(p['witnesses'])==len(c['witnesses'])==len(n['witnesses'])==17 and len(p['source'])==95 and len(c['source'])==94 and len(n['source'])==111
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
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
def run(g):
 env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};rows={}
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
a,b=run(p),run(c);assert a[p['output']]==b[c['output']]
res=['A0','A1','auxResidual','g72','rankDifference','zDifference','dDifference','vDifference']
assert all(a[x]==b[x] for x in res)
out=b[c['output']];inputs=set(c['witnesses']);degree=lambda mon:sum(x in inputs for x in mon)
assert max(map(degree,out))==20
witness=tuple(sorted(['Y']*8+['eta']*8+['i']*4));coeff={tuple(x for x in mon if x not in inputs):v for mon,v in out.items() if tuple(x for x in mon if x in inputs)==witness}
assert coeff=={():1}
print(json.dumps({'scope':'independent all-port exact integer polynomial and liveness comparison; no Lean', 'variables':17,'positive_operations':94,'natural_operations':111,'input_degree':20,'output_terms':len(out),'all_residuals_equal':len(res),'degree_witness_coefficient':str(coeff),'all_inputs_ports_and_rows_live':True,'lean_elaboration':False},sort_keys=True,indent=2))
