#!/usr/bin/env python3
"""Independent linear-growth 87 guard source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-guard-strict-linear-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'GuardStrict87Linear.lean','2fd3457167b2631db7a22181f95fc99d29c430d076168bce9e2ee47bd292809e').decode()
pin(A/'check_source.py','0d55f1ce780e02781f0e834dbe2b6df93c794beacfbb84a9874b723059ed4c11')
receipt=pin(A/'observation.json','04a0009f03d1a038a5769436d06443b247ff4daef4e1b76686375d9061222875')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-guard-strict-linear-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='24e33fe3167cf5629d4e432cd71ef2ee4efb381d3408814ee9d4fa1eb02f10b9'
for f in ('(hX : q beta v≤v 6)','have hFX : v 1<v 6 := lt_of_lt_of_le hF hX',
 'GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'have hnat : bb*v 13+v 1=cc*(v 6+K*qq)',
 'exact (mul_lt_mul_left hb).mp hmul'):
 assert f in s,f
n=0
for q,F,a,X,K in itertools.product(range(3,13),range(1,5),range(1,5),range(1,100),range(5)):
 if F+a>=q or X<q or X>=q*q:continue
 b=q-1;C=q-F-a;z=C*(X+K*q)-F
 if z%b:continue
 omega=z//b
 assert omega>0 and C*K<omega
 n+=1
assert n>0
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-87-guard-strict-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'conditional linear-growth source review; no Lean or derived growth',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'strictly_new_bounded_cases':n},sort_keys=True,indent=2))
