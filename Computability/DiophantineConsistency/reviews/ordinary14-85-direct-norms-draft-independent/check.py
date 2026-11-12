#!/usr/bin/env python3
"""Independent direct 85 norm source/finite review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-direct-norms-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'DirectNorms85.lean','2b07f618dc5e76fd6e274596d4425c5c76dbd60919014febb024a9a99265c622').decode()
pin(A/'check_source.py','23c5034e703dc967a1f92a955a50e6fa7975d9e53d7abb2a8e749765f79a92f9')
receipt=pin(A/'observation.json','69c01872c2e4f2834cd68ce8f771433fb39358e18327bfcf0d2750398aab5f89')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-direct-norms-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='658ded0f7288b03a53949339f26a490ef2a3dc0d49c54613906641be2629e4bb'
for path,h in {
 'ordinary14-85-guard-rank-draft/GuardRank85.lean':'e9eb6ebef3d35dfa2324e00e16a068f7ad67e680f79ebee3a4f8af156e3c6d55',
 'ordinary14-direct-first-root-model-draft/FirstRootBridge.lean':'92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f',
 'ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean':'771cc1bf65a1d0e2b195627a45a4d152671ed0e86dbf12516855bfe8f1c11216',
}.items():pin(D/'research'/path,h)
g=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('def X (v : Fin 14 → V) : V := v 6',
 '(hbeta : 0<beta) (hJ : 0<v 0) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 '(ZeroFields8485Draft.fields85 p v hz).1',
 '(ZeroFields8485Draft.fields85 p v hz).2.2.2.1',
 'root_of_scaled_residual (scale beta v) (firstP beta v) (v 8) (radicand beta v) hM hD hf',
 'strong_norm_of_ring_residual _ _ _ _ hg'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-guard-rank-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8501021);nondiv=0
for _ in range(600):
 v={n:rng.randrange(0,8) for n in g['witnesses']+g['fixed_numerals']};z=calc(v)
 q=1+v['J']*v['beta'];X=v['X'];Y=q**3*v['s'];k=v['eta']+v['zeta']
 a=X*Y+Y;c=v['eta']+Y*k;delta=3+4*a+a*a;ell=X*Y*Y*k;M=q**3*v['J']*v['beta']
 assert z['A0']==M*M*((ell+k-v['r'])**2-(1+ell*(ell+k)))
 assert z['g72']==(v['i']*c*c)**2-delta*(v['f']**2-1)
 nondiv+=X%q!=0
assert nondiv
print(json.dumps({'scope':'source and finite literal controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'field_controls':600,
 'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
