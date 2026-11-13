#!/usr/bin/env python3
"""Exact formal polynomial check of a negative reconstructed local coordinate."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;raw=(P.parent/'nine-sharing-sign27-sextic-normalized-root-candidate/seed.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d';s=json.loads(raw)
# Sparse formal polynomial in independent integer indeterminates a and K.
def const(v):return {(0,0):v} if v else {}
def add(x,y,sign=1):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+sign*v
 return {k:v for k,v in z.items() if v}
def mul(x,y):
 z={}
 for (i,j),v in x.items():
  for (k,l),w in y.items():z[(i+k,j+l)]=z.get((i+k,j+l),0)+v*w
 return {k:v for k,v in z.items() if v}
a={(1,0):1};K={(0,1):1};one=const(1);H=add(mul(a,add(K,one)),one)
# a=beta, v1=v2=0, v3=-2, v9=H-K-1, v4=H+K+1, gap=a²-1.
v={1:const(0),2:const(0),3:const(-2),4:add(add(H,K),one),9:add(add(H,K,-1),one,-1),22:add(mul(a,a),one,-1)};p={'beta':a,'K0':K}
def evaluate(t):
 op=t[0]
 if op=='num':return const(t[1])
 if op=='var':return v[t[1]]
 if op=='port':return p[t[1]]
 x,y=evaluate(t[1]),evaluate(t[2]);return mul(x,y) if op=='mul' else add(x,y,1 if op=='add' else -1)
rows={r['gate']:r['expr'] for r in s['residuals']};assert evaluate(rows['gap'])=={} and evaluate(rows['Nt'])=={}
# For all a>=1, K>=0, v9=(a-1)K+a, v4=a(K+1)+K+2 and gap=a²-1 are nonnegative; v3=-2.
assert v[9]=={(1,1):1,(1,0):1,(0,1):-1} and v[4]=={(1,1):1,(1,0):1,(0,1):1,(0,0):2}
print(json.dumps({'status':'PASS_FORMAL_LOCAL_COUNTEREXAMPLE','source_sha256':hashlib.sha256(raw).hexdigest(),'parameters':'all integer a>=1 and K>=0','assignment':'beta=a, K0=K, v1=v2=0, v3=-2, v9=(a-1)K+a, v4=a(K+1)+K+2, gap=v22=a²-1','identities':'gap residual = Nt residual = 0 in Z[a,K]','scope':'only gap and Nt; no assertion other residuals vanish, and no counterexample to the full system'},indent=2,sort_keys=True))
