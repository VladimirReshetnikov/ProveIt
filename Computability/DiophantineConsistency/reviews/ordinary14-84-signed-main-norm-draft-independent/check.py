#!/usr/bin/env python3
"""Independent signed-main source composition review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-signed-main-norm-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
src=pin(A/'SignedMainNorm.lean','b674de377bdae3155ffb46b1711971425a68cdaa1ac9134c608a3233bc8c5e8b').decode()
pin(A/'check_source.py','e1fa6993e6c85857b18423a967f5fb8124aa9b07fe599972b8233a0966e3d580')
receipt=pin(A/'observation.json','22cc793823de1a9146a337289082bd8c112f24b0b82120b9ef7c2c43c09685a3')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-signed-main-norm-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='76de549769369f350c0e6f6015aa537da1c67848164c0471ff2572e8a7649c41'
for path,h in {
 'ordinary14-84-main-norm-client-draft/MainNormClient.lean':'58a05ca5998323ad4665ad03a3f0a580c579ed95b210dfc803ecfe8a9e48b767',
 'ordinary14-scaled-signed-root-draft/SignedScaledRoot.lean':'900ff0f8acda716fe01f96ffdd463636fae411149df172946e1c34d27ab8cadd',
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
}.items(): pin(D/'research'/path,h)
for f in ('(hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'AuxGraphNormClientDraft.mainValue p beta v=ι (AuxGraphNormClientDraft.U beta v*d) ∨',
 'AuxGraphNormClientDraft.mainValue p beta v= -ι (AuxGraphNormClientDraft.U beta v*d)',
 '(ZeroFields8485Draft.fields84 p v hz).2.1',
 'rw [MainNorm84Draft.shared_main p] at hmain',
 'AuxGraphNormClientDraft.main_eval p beta v hport',
 'scaled_signed_root _ _ _ hU (sub_eq_zero.mp hmain)'):
 assert f in src,f
def replay(script,receipt):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==receipt
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-main-norm-client-draft-independent','ordinary14-scaled-signed-root-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source and dependency review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_dependency_reviews':2},sort_keys=True,indent=2))
