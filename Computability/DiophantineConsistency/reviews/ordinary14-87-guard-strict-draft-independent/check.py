#!/usr/bin/env python3
"""Independent conditional 87 strict guard bound review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-guard-strict-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'GuardStrict87.lean','ae5023f9eb2de4ff623540d5d72a7007eabc1935058f64a67347cc3bc6dbdedb').decode()
pin(A/'check_source.py','cd39da0b8347544fc225cbb14a3adcd4b9bfc7842620651cfb2d8e58ad65eeca')
receipt=pin(A/'observation.json','f1adbcfe246b170c311d0f47849d208e3bad2b422101593b94a3cb6729166945')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-guard-strict-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='58410e77d0568d5f93cff512814e85a3aadeb9aa3d1331156d96b020f0859486'
for f in ('(hbeta : 0<beta)', '(hX : q beta v*q beta v≤v 6)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'have hCcast : ι cc=ι qq-ι (v 1)-ι (v 2) := cast_C beta v hgap',
 'have hnat : bb*v 13+v 1=cc*(v 6+K*qq)',
 'exact (mul_lt_mul_left hb).mp hmul'):
 assert f in s,f
n=0
for q,F,a,X,K in itertools.product(range(3,13),range(1,5),range(1,5),range(9,170),range(5)):
 if F+a>=q or X<q*q:continue
 b=q-1;C=q-F-a; z=C*(X+K*q)-F
 if z%b:continue
 omega=z//b
 assert omega>0 and C*K<omega
 n+=1
assert n>0
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-guard-gap-draft-independent','ordinary14-86-to-87-positive-map-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'conditional source guard-bound review; no Lean or derived growth',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'bounded_guard_cases':n},sort_keys=True,indent=2))
