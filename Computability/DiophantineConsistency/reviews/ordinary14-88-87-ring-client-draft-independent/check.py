#!/usr/bin/env python3
"""Independent 88→87 exact ring/graph source review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-87-ring-client-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'RingComparison88To87.lean','57e97e72f3eae93c93daa1bff8cc30e7b9de4850a6f8745baeb53b57c4c7c8f8').decode()
pin(A/'check_source.py','03cc43acb790475f12c407f884b666e18bca574ec73e0a6721dcbe2b697b9183')
receipt=pin(A/'observation.json','d2469a376c967f9144b26cf2c972ac236b440b7ad7b2072790724977d240d1f0')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-87-ring-client-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='268bfb80e89646750d38c737dd5491707b12bcf48f156dafdd344b32434b9311'
pin(D/'research/ordinary14-guarded-fold88-lean-draft/P88QuotientGuardedGraph.lean','85d347c35b4ea21fe20651460c0df6f20adf0cc444f99b4e3c9a8a9d81d0097e')
pin(D/'research/ordinary14-shifted-guard87-lean-draft/P87ShiftedGuardGraph.lean','d6fef15cc23f89125d7d8720b81567e05bb71fd18e83f925e307f4b428e9c279')
for f in ('Function.update v 13 (v 13+v 1)',
 'C*(X+K*(1+b))-F-b*(t+F)=C*(X+K*(1+b))-F*(1+b)-b*t',
 '(P87ShiftedGuard.graph p).output.evalRing (transform v)',
 '(P88QuotientGuarded.graph p).output.evalRing v'):
 assert f in s,f
# Exact polynomial normalization over Z[b,C,X,K,F,t].
def plus(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {k:v for k,v in c.items() if v}
one={(0,)*6:1}; b,C,X,K,F,t=({tuple(int(i==j) for i in range(6)):1} for j in range(6))
base=mul(C,plus(X,mul(K,plus(one,b))))
left=plus(plus(base,neg(F)),neg(mul(b,plus(t,F))))
right=plus(plus(base,neg(mul(F,plus(one,b)))),neg(mul(b,t)))
assert left==right
old=json.loads((D/'research/ordinary14-guarded-fold88-26/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
def ev(g,values,ports,mod):
 v=dict(zip(g['witnesses'],values));v.update(dict(zip(g['fixed_numerals'],ports)))
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=(x+y if op=='+' else x-y if op=='-' else x*y)%mod
 return v
rng=random.Random(881387)
for mod in (12,97):
 for _ in range(100):
  v=[rng.randrange(mod) for _ in range(14)];p=[rng.randrange(mod) for _ in range(4)]
  w=v.copy();w[13]=(v[13]+v[1])%mod
  a=ev(old,v,p,mod);z=ev(new,w,p,mod)
  assert all(a[x]==z[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88→87 ring polynomial and source review; no Lean or positive map',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'finite_ring_controls':200},sort_keys=True,indent=2))
