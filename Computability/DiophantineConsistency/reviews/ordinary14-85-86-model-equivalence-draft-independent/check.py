#!/usr/bin/env python3
"""Independent 85/86 positive equivalence source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-86-model-equivalence-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'ModelEquivalence85To86.lean','f540a89b57f708e15f641f25e7a2a6bf774a8b68899d7dcd4643b34851480157').decode()
pin(A/'check_source.py','2e430ba7c13401ae0d9218cfe4da93f8244384c86d2eb9814c3edc7a60b6ec14')
receipt=pin(A/'observation.json','bd711828b3d90e0d11299797c60fa8781e53e2b76779ec379dd6cd6a2d13d56b')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-86-model-equivalence-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='75b32b83b0369fa126daab6600a757c39fd8b4a497e17a3cf6c13ecec9283afb'
for path,h in {
 'ordinary14-85-to-86-positive-map-draft/PositiveMap85To86.lean':'9f87b9676e4b82db7c622ab6ff4029176e96e0e0ad845a029eb07f4d005c0b56',
 'ordinary14-86-to-85-fresh-map-draft/FreshMap86To85.lean':'3f8bb56132c5362630d1d43612a8812b88d2a36e4ba407e3ee93990dababdce7',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/Compact44/P72Root.lean','066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 'InternalZero (P85QcubeGraph.graph p).output v) ↔',
 'InternalZero (P86ResidueGraph.graph p).output v)',
 'PositiveMap85To86Draft.positive_map p beta v hport hv hz',
 'FreshMap86To85Draft.positive_map p beta v hbeta hport hv hz',
 'theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)',
 'P72Root.cast_port p 0'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-to-86-positive-map-draft-independent','ordinary14-86-to-85-fresh-map-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source interface and dependency review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_direction_reviews':2},sort_keys=True,indent=2))
