#!/usr/bin/env python3
"""Independent full-output all-port equality for factored-root graph."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
c=json.loads(pin('research/adaptive-aq20-factored-root103/candidate.json','970b279d7e1a5d063c5e9b842fa92cb8a53827738bfa5af8ba42d93a36d97e7e'))
n=json.loads(pin('research/adaptive-aq20-factored-root103/natural-candidate.json','ef393ed2e2309e7c121c6fe90e91e5118cd2db9f39c9f13cb9372e9560508f01'))
pin('research/adaptive-aq20-factored-root103/receipt.json','33f38c8a9e62fc31d68b879580fef3424e2dd9776e3d1d25bfdf990efd401767')
pin('reviews/adaptive-aq20-substituted-scales104-independent/result.json','b1afbc50dc3a450be310cee4f102f1e0796aaf38c20d107ea5924aff3902901a')
assert len(p['witnesses'])==len(c['witnesses'])==len(n['witnesses'])==20 and len(p['source'])==104 and len(c['source'])==103 and len(n['source'])==123
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
res=['A0','A1','auxResidual','g72','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
assert all(a[x]==b[x] for x in res)
out=b[c['output']];inputs=set(c['witnesses']);degree=lambda mon:sum(x in inputs for x in mon)
assert max(map(degree,out))==14
witness=tuple(sorted(['J']*10+['X']*2+['eta']*2));coeff={tuple(x for x in mon if x not in inputs):v for mon,v in out.items() if tuple(x for x in mon if x in inputs)==witness}
assert coeff=={('beta',)*10:1}
print(json.dumps({'scope':'independent all-port exact integer polynomial and liveness comparison; no Lean', 'variables':20,'positive_operations':103,'natural_operations':123,'input_degree':14,'output_terms':len(out),'all_residuals_equal':len(res),'degree_witness_coefficient':str(coeff),'all_inputs_ports_and_rows_live':True,'lean_elaboration':False},sort_keys=True,indent=2))
