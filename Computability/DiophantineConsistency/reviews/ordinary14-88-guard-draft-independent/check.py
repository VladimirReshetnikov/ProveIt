#!/usr/bin/env python3
"""Independent 88 own-zero quotient guard source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-guard-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Guard88.lean','16d69f0a701c3485a9de0b5c6f6945ecbce29cfc697ed219a3803b5cdba8e815').decode()
pin(A/'check_source.py','19f4b11cdbbdc02bbac8029d4ca62d0b69e2126f555348c9011e6d208c5141ef')
receipt=pin(A/'observation.json','8cdd5a8762ec4581831b5b3fe26b9e50c2b9a8dbd568b28b68d3bf456ebc416c')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-guard-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='3eae899e4a9225244e6d19e79b196b119ace82b81469cd34641ff8886c81f173'
for f in ('P88QuotientGuarded.output_shape','(eval (P88QuotientGuarded.graph p).aux v-1)',
 '(eval (P88QuotientGuarded.graph p).Bt v-eval (P88QuotientGuarded.graph p).b v*ι (v 13))',
 'sub_eq_zero.mp ((fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).2.2.2.2',
 '(hport : (p 0 : DiffRing V)=ι beta)',
 'eval (P88QuotientGuarded.graph p).Bt v=ι ((v 0*beta)*v 13)'):
 assert f in s,f
n=0
for fields in itertools.product(range(-2,3),repeat=5):
 if sum(x*x for x in fields)==0:assert fields[-1]==0;n+=1
assert n==1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 own-zero quotient guard source review; no Lean','finite_zero_cases':n},sort_keys=True,indent=2))
