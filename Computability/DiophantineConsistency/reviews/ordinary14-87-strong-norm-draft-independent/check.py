#!/usr/bin/env python3
"""Independent 87 direct-Y strong norm source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-strong-norm-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'StrongNorm87.lean','2416b1b1046248abe1b2a6b339d81e89838fdfc65c2189970e4e00d25b5fbf11').decode()
pin(A/'check_source.py','9df42ff381ab6fd86c3f3d95809bfb0a77bf3965e6b278cd2a38e780658e8b65')
receipt=pin(A/'observation.json','bfd5d5b563e7c7fcce3d6dfa17c3442bcf4c83e55f99aa909c6284d4e64dd39b')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-strong-norm-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='959ae4dd4a7dcb69323bcf682c19d16ac1aeaec6cfdd8936e1e8c3f7bb483fe1'
for f in ('def a (v : Fin 14 → V) : V := v 6*v 7+v 7',
 'def c (v : Fin 14 → V) : V := v 9+v 7*k v',
 'def Delta (v : Fin 14 → V) : V := 3+4*a v+a v*a v',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 '(FourFields87Draft.fields_of_zero p v hz).2.2.2',
 'exact strong_norm_of_ring_residual _ _ _ _ hg'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
n=0
for x in range(-3,4):
 for y in range(-3,4):
  a=x*y+y;delta=3+4*a+a*a
  for c in range(-3,4):
   for i in range(-3,4):
    for f in range(-3,4):
     z=(i*c*c)**2-delta*(f*f-1)
     assert (z==0)==((i*c*c)**2+delta==delta*f*f)
     n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-four-fields-draft-independent','ordinary14-aux-ring-norm-extraction-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero strong norm source review; no Lean',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'finite_algebra_cases':n},sort_keys=True,indent=2))
