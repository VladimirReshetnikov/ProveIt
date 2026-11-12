#!/usr/bin/env python3
"""Independent first-norm source and finite review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-first-norm-client-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstNormClient.lean','557f24cb4cc6184a3830feb01f4d70a7c228929c1f264d6dd79c07ab15b25142').decode()
pin(A/'check_source.py','840fd08fdd34fe9718360a14242cb95485799092ff7d4b8b7db7ea551e9227f7')
receipt=pin(A/'observation.json','c600371ac58d88d53995de07933c0a2b39328b9d61dfdb0c9882a3ec76f76ca9')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-first-norm-client-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='c090e0c6a4b5631e97d0cc9cfd6a771fc4c600cc2ede8c6660829b9eb87a5fbc'
for path,h in {
 'ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'ordinary14-direct-first-root-graph-client-draft/GraphFirstRootClient.lean':'864fb3935afd53711562656a3d5cbf7473d9182ded7face06b72416f6d72a78a',
 'ordinary14-direct-first-root-positive-client-draft/PositiveClient.lean':'888f0d0641246eedfdcafdffafa32d0986a46a5db4106196b20e7e48472aeda3',
 'ordinary14-direct-first-root-model-draft/FirstRootBridge.lean':'92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f',
}.items():pin(D/'research'/path,h)
graph=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '(ZeroFields8485Draft.fields84 p v hz).1','old_first_eval p beta v (v 8) hport',
 'rw [putRoot_self] at he','root_of_scaled_residual (scale beta v) (firstP beta v) (v 8) (radicand beta v)',
 '(scale_positive beta v hbeta hJ) (radicand_positive beta v) hf'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-85-zero-fields-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in graph['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(841001);positive=negative=zero=0
for _ in range(500):
 v={n:rng.randrange(0,6) for n in graph['witnesses']+graph['fixed_numerals']}
 z=calc(v);q=1+v['J']*v['beta'];X=q*v['w'];Y=q**3*v['s'];k=v['eta']+v['zeta']
 ell=X*Y*Y*k;P=ell+k;rad=1+ell*P;scale=q**3*v['J']*v['beta'];diff=P-v['r']
 assert z['A0']==scale*scale*(diff*diff-rad) and rad>0
 positive+=diff>0;negative+=diff<0;zero+=diff==0
assert positive and negative and zero
# A zero scale makes the first residual vanish even when the magnitude is zero.
assert 0*0*(0*0-1)==0 and 0*0!=1
print(json.dumps({'scope':'source and finite first-field controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'formula_cases':500,
 'positive_differences':positive,'negative_differences':negative,'zero_differences':zero,
 'zero_scale_boundary':True},sort_keys=True,indent=2))
