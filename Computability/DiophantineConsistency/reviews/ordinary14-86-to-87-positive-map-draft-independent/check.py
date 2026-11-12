#!/usr/bin/env python3
"""Independent positive 86→87 model-map source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-to-87-positive-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'PositiveMap86To87.lean','439e4e88a6fa490c63e213c9434620d8e4459a2573b3b4d94993d9d369b510d5').decode()
pin(A/'check_source.py','f04ec1d63865b567f76c9a3fac2e94712654cbc730f00530e5488af2471f55f2')
receipt=pin(A/'observation.json','3c21feef64df27b7f408329ed4e1ec857e29da96daeea8f29e6db38b5c031a5b')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-to-87-positive-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='b311fff855bd696cb3c7ee71ad84d205bd4e3cf9805a2f7beee236b0630adbd2'
for f in ('(hgap : v 1+v 2<q beta v)','P72Root.ι_tsub hF','P72Root.ι_tsub (le_of_lt ha)',
 'Function.update v 13 (v 13+C beta v*K)',
 'GuardGap86Draft.gap_of_86_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'rw [←cast_forward p beta K v hport hK hgap] at h','rw [h]'):
 assert f in s,f
n=0
for q,F,a,K,h in itertools.product(range(1,12),range(1,6),range(0,6),range(5),range(1,6)):
 if F+a<q:
  C=max(0,max(0,q-F)-a)
  assert C==q-F-a and h+C*K>0
  n+=1
assert n>0
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-86-guard-gap-draft-independent','ordinary14-86-87-ring-client-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source and conditional positive-map review only; no Lean','prelink_readme_sha256':sha(r[:-len(tail)]),'bounded_gap_cases':n},sort_keys=True,indent=2))
