#!/usr/bin/env python3
"""Exact upper bound and fixed-port modular lower witness for the draft degree."""
from pathlib import Path
from hashlib import sha256
import gzip,json,sys
if sys.flags.optimize: raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent
D=H.parents[1]
G=H/'graph-dag.json'
C=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients'
B=C/'BINDING.json'
def need(x,m):
 if not x: raise RuntimeError(m)
def sha(p): return sha256(p.read_bytes()).hexdigest()
need(sha(G)=='82dd1f55f67ef3487509a6d4d31ef085d5d4813c11df43be40570a3293a8b430','graph drift')
need(sha(B)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01','binding drift')
g=json.loads(G.read_text()); bind=json.loads(B.read_text())
rows={n:[op,x,y] for n,op,x,y in g['source']}
shape={'vn':['+','V','n'],'vn2':['*','vn','vn'],'polarV2':['*','V','V'],
 'polarQV2':['*','Q','polarV2'],'polarCy':['-','polarQV2',1],'oneQ':['-',1,'Q'],
 'polarHpart':['*','oneQ','vn2'],'h':['+','polarHpart','polarCy']}
need(all(rows[n]==r for n,r in shape.items()),'h shape')
# Exact h = (V+n)^2 - 1 - Q*n*(2*V+n), checked as sparse polynomials.
def add(a,b,sgn=1):
 d=a.copy()
 for m,c in b.items(): d[m]=d.get(m,0)+sgn*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for (i,j,k),c in a.items():
  for (l,m,n),e in b.items():
   t=(i+l,j+m,k+n);d[t]=d.get(t,0)+c*e
 return {m:c for m,c in d.items() if c}
one={(0,0,0):1};Q={(1,0,0):1};V={(0,1,0):1};n={(0,0,1):1};vn=add(V,n)
left=add(mul(add(one,Q,-1),mul(vn,vn)),add(mul(Q,mul(V,V)),one,-1))
right=add(add(mul(vn,vn),one,-1),mul(mul(Q,n),add(add(V,V),n)),-1)
need(left==right,'h cancellation identity')
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']})
for n,op,x,y in g['source']:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0
 deg[n]=dx+dy if op=='*' else max(dx,dy)
 if n=='h':
  need((deg['Q'],deg['V'],deg['n'])==(14,8,1),'h degree premises')
  deg[n]=max(2*max(deg['V'],deg['n']),deg['Q']+deg['n']+max(deg['V'],deg['n']))
upper={n:deg[n] for n in ['Q','V','h','den','polarT','polarA','polarCorrection','N','A0','A1','P12']}
need(upper['P12']==172,'degree upper')
p=1000000007;vals={name:[0,i+2] for i,name in enumerate(g['witnesses'])}
for name in g['fixed_numerals']:
 meta=bind['ports'][name];f=C/meta['file'];z=f.read_bytes();raw=gzip.decompress(z)
 need(sha256(z).hexdigest()==meta['sha256_gzip'] and sha256(raw).hexdigest()==meta['sha256_raw'] and len(raw)==meta['raw_bytes'],'payload drift '+name)
 vals[name]=[int.from_bytes(raw,'little')%p]
def poly(op,a,b):
 if op=='*':
  z=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
 else:z=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
for n,op,x,y in g['source']:
 vals[n]=poly(op,vals[x] if isinstance(x,str) else [x],vals[y] if isinstance(y,str) else [y])
need(len(vals['P12'])-1==172 and vals['P12'][-1]==960910299,'modular lower witness')
print(json.dumps({'status':'PASS','graph_sha256':sha(G),'upper_degrees':upper,
 'modulus':p,'linear_witness_coefficients':list(range(2,14)),'lower_degree':172,
 'lower_leading_coefficient':vals['P12'][-1]},indent=2))
