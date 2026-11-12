#!/usr/bin/env python3
"""Independent positive balance composition review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-positive-main-balance-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'PositiveMainBalance.lean','89e879da8772594d6da35d55a54512e9378812cdff526d1a5020987605febc4f').decode()
pin(A/'check_source.py','5e5d7f3f14542e902d93d6e637eb6e3770d2e81f0cac3a8ca90449f9dc768aec')
receipt=pin(A/'observation.json','e5e4bdb6648b0af5b0038fbd585f4fcd93a4d56a4e9bc89c26dcf218ee839462')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-positive-main-balance-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='82257d95b1474a3bd09ff954fa5c7e681252482582610ea839e1307d370f3bc8'
for path,h in {
 'ordinary14-84-own-zero-main-balance-draft/OwnZeroMainBalance.lean':'4c98fabd9e270d181a6774bc61abd54f92a0b03dfaf680349d62f00e45351382',
 'ordinary14-84-qcube-size-draft/QCubeSize.lean':'6553261e396c24659988420260324bc19911ade97854405e863db4bfb6e510cc',
}.items():pin(D/'research'/path,h)
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)',
 '(hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'Y_at_least_eight beta v hbeta (hv 0) (hv 7)',
 'OwnZeroMainBalance84Draft.norm_and_balance p beta K MC MF v hport hK hMC hMF hv hY hz'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-own-zero-main-balance-draft-independent','ordinary14-84-qcube-size-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source composition review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_dependency_reviews':2},sort_keys=True,indent=2))
