#!/usr/bin/env python3
"""Independent exact polynomial and graph review, without Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-87-ring-client-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
src=pin(A/'RingComparison86To87.lean','5b72fe231dfb726019164de8b64eb4875d0929b08493a281696ffb4c33d66075').decode()
pin(A/'check_source.py','f930c8ae28be4abbd22edf9412991a94fc4f010276aa515fdc8a16dfa69c37aa')
receipt=pin(A/'observation.json','b066c9220bcf093aa95404dafdb119fe134fb5971c92a59cecebc7700691ef42')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-87-ring-client-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='06164eacff91bb143494a63eb1445c906cfab02a4908f8f0e8d8a8422604dbfa'
pin(D/'research/ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean','5b655c426151d999745360c8366f940198fcaa1a8408eb905b6b92285a9dcf42')
pin(D/'research/ordinary14-shifted-guard87-lean-draft/P87ShiftedGuardGraph.lean','d6fef15cc23f89125d7d8720b81567e05bb71fd18e83f925e307f4b428e9c279')
for f in ('Function.update v 13 (v 13+((1+v 0*(p 0 : R))-v 1-v 2)*(p 1 : R))',
 'C*(X+K*(1+b))-F-b*(h+C*K)=C*(X+K)-F-b*h',
 '(P87ShiftedGuard.graph p).output.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).output.evalRing v'):
 assert f in src,f
# Independent expansion of the guard difference in Z[b,C,X,K,F,h].
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
one={(0,)*6:1}; b,C,X,K,F,h=({tuple(int(i==j) for i in range(6)):1} for j in range(6))
left=plus(plus(mul(C,plus(X,mul(K,plus(one,b)))),neg(F)),neg(mul(b,plus(h,mul(C,K)))))
right=plus(plus(mul(C,plus(X,K)),neg(F)),neg(mul(b,h)))
assert left==right
old=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def ev(g,v,mod):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=((x+y if op=='+' else x-y if op=='-' else x*y)%mod)
 return v
rng=random.Random(871386)
for mod in (12,97):
 for _ in range(100):
  v={x:rng.randrange(mod) for x in new['witnesses']+new['fixed_numerals']};a=ev(new,v,mod)
  w={x:v[x] for x in old['witnesses'] if x!='omega'};w.update({x:v[x] for x in old['fixed_numerals']});w['omega']=(v['h']+a['C']*v['K0'])%mod
  z=ev(old,w,mod)
  assert all(a[x]==z[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'source and ring-polynomial review only; no Lean or positive-map theorem',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'finite_ring_controls':200},sort_keys=True,indent=2))
