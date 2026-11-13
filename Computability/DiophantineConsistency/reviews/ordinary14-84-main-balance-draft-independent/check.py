#!/usr/bin/env python3
"""Independent natural-balance source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-main-balance-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'MainBalance.lean','b06ab81424dee0633ab4ad83d4fabc0a49c232f765f9e10401b74d46a3622a8b').decode()
pin(A/'check_source.py','28ed054c9a2b0de5f5c9145fc95bfd20d03f52cb91edee8e265ff7f0ead91131')
receipt=pin(A/'observation.json','a82e840eab0c7a6db489edfe7a76e118bda5c60eb6d8da5cfe4fb36fbc5f0f5d')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-main-balance-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='8a29a6da777e7c4e863b47ed6f3e4165f63bd9b4139c42eb91f4e2f2e084b783'
for path,h in {
 'ordinary14-84-main-orientation-draft/MainOrientation.lean':'33887b86870acc88bce72c91db03a355156ddf8980a48de55dfe4144d7dface4',
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
}.items():pin(D/'research'/path,h)
for f in ('(hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)',
 '(hY : 8≤AuxGraphNormClientDraft.Y beta v)',
 '(hk : 0<AuxGraphNormClientDraft.k v)',
 '(hR : AuxGraphNormClientDraft.rank p beta v=ι R)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'U*d+H*AuxGraphNormClientDraft.k v=U*(X+a*c)+H*(U*v 12+R+1)',
 'oriented_main_root p beta v R hport hs hY hk hR hz',
 'simpa only [map_mul] using hr.symm','apply ι_injective','rw [hroot]'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-main-orientation-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=below=above=0
for U in range(1,5):
 for X in range(1,5):
  for Y in range(8,11):
   for R in range(4):
    for W in range(4):
     k=R+1+U*W;eta=2;a=X*Y+Y;c=eta+Y*k;H=3+4*a
     for gamma in range(4):
      d=X+a*c+H*(gamma-W)
      if d<0:continue
      signed=U*(X+a*c)+H*(U*gamma-(k-R-1))
      assert signed==U*d and U*d+H*k==U*(X+a*c)+H*(U*gamma+R+1)
      cases+=1;below+=gamma<W;above+=gamma>W
assert below and above
print(json.dumps({'scope':'conditional source and finite controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'balance_cases':cases,
 'gamma_below_W':below,'gamma_above_W':above},sort_keys=True,indent=2))
