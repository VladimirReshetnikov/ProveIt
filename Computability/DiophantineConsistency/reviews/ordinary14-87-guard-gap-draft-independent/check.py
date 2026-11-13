#!/usr/bin/env python3
"""Independent 87 own-zero guard-gap source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-guard-gap-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'GuardGap87.lean','92d1dcd67df9c0b7e22d4ca2bf0e54d86d11a443892209c14e4f832010ac2988').decode()
pin(A/'check_source.py','8d0b3bb3c713882d13358d349a4e8cc36dd60376220557938ebe83c252149430')
receipt=pin(A/'observation.json','216d78891c8adb349b95232c7daa4590cff5c84a222574840449e9f5f14bfe25')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-guard-gap-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='fd8146a95e04bfc6ead01825a5534451d1c186b9a19084e60d99a9a8f4dab59d'
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 '(eval (P87ShiftedGuard.graph p).aux v-1)',
 'fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).2.2.2.2',
 '(ι (v 6)+ι K*ι (AuxGraphNormClientDraft.q beta v))',
 '(hF : 0<v 1) (hw : 0<v 6)','have hg := guard_of_zero p v hz',
 'mul_nonpos_of_nonpos_of_nonneg','exact ι_lt_ι.mp hlt'):
 assert f in s,f
n=0
for q,F,a,X,K,b,h in itertools.product(range(1,10),range(1,5),range(5),range(1,5),range(4),range(5),range(5)):
 if (q-F-a)*(X+K*q)-F-b*h==0:
  n+=1;assert F+a<q
assert n>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'87 own-zero source and finite guard review only; no Lean','prelink_readme_sha256':sha(r[:-len(tail)]),'bounded_guard_zeros':n},sort_keys=True,indent=2))
