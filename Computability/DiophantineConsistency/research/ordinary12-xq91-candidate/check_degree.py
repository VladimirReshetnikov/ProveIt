#!/usr/bin/env python3
"""External exact-degree certificate for the retained fixed-port 91 graph."""
from pathlib import Path
from hashlib import sha256
import gzip,json,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent; D=H.parents[1]
G=H/'candidate.json'; B=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
def digest(p):return sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(digest(G)=='fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513','graph drift')
need(digest(B)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01','binding drift')
g=json.loads(G.read_text());binding=json.loads(B.read_text()); rows=g['source']
lookup={r[0]:r[1:] for r in rows}
need(all(lookup[k]==v for k,v in {'vn':['+','V','n'],'vn2':['*','vn','vn'],'polarV2':['*','V','V'],
 'polarQV2':['*','Q','polarV2'],'polarCy':['-','polarQV2',1],'oneQ':['-',1,'Q'],
 'polarHpart':['*','oneQ','vn2'],'h':['+','polarHpart','polarCy']}.items()),'h graph shape')
def add(a,b):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 z={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));z[k]=z.get(k,0)+va*vb
 return {k:v for k,v in z.items() if v}
one={(0,0,0):1}; Q={(1,0,0):1};V={(0,1,0):1};n={(0,0,1):1};vplus=add(V,n)
lhs=add(mul(add(one,neg(Q)),mul(vplus,vplus)),add(mul(Q,mul(V,V)),neg(one)))
rhs=add(add(mul(vplus,vplus),neg(one)),neg(mul(mul(Q,n),add(add(V,V),n))))
need(lhs==rhs,'h polynomial identity')
degree={n:1 for n in g['witnesses']};degree.update({n:0 for n in g['fixed_numerals']});degree.update({n:0 for n in range(5)})
tight=degree.copy()
for name,op,a,b in rows:
 degree[name]=degree[a]+degree[b] if op=='*' else max(degree[a],degree[b])
 tight[name]=tight[a]+tight[b] if op=='*' else max(tight[a],tight[b])
 if name=='h':tight[name]=max(2*max(tight['V'],tight['n']),tight['Q']+tight['n']+max(tight['V'],tight['n']))
need(tight['P12']==172,'unexpected degree upper bound')
P=1_000_000_007;v={n:[0,i+2] for i,n in enumerate(g['witnesses'])};v.update({n:[n] for n in range(5)})
for name in g['fixed_numerals']:
 meta=binding['ports'][name];source=B.parent/meta['file'];z=source.read_bytes()
 need(sha256(z).hexdigest()==meta['sha256_gzip'],'compressed payload drift '+name)
 raw=gzip.decompress(z);need(sha256(raw).hexdigest()==meta['sha256_raw'] and len(raw)==meta['raw_bytes'],'raw payload drift '+name)
 v[name]=[int.from_bytes(raw,'little')%P]
def calc(op,a,b):
 if op=='*':
  z=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 else:z=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(z)>1 and z[-1]==0:z.pop()
 return z
for name,op,a,b in rows:v[name]=calc(op,v[a],v[b])
need(len(v['P12'])-1==172 and v['P12'][-1]==960910299,'degree lower witness')
print(json.dumps({'status':'PASS','syntactic_degree_upper':degree['P12'],'tight_degree_upper':tight['P12'],
 'witness_degree_mod_prime':len(v['P12'])-1,'leading_mod_prime':v['P12'][-1],
 'prime':P,'substitution':'witness i maps to (i+2)*t',
 'degree_labels':{k:tight[k] for k in ('Y','X','A0','A1','Q','V','h','den','polarT','polarA','polarCorrection','N','P12')}},indent=2))
