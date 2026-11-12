#!/usr/bin/env python3
"""Independent 13-parent four-field source extraction review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-four-fields-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentFourFields.lean','d3944637ce77c95145a45ef0d225e8e3de702b991609fc272fafe403e408ca29').decode()
pin(A/'check_source.py','cb9d5a2fdaa3a86866093557dcd60a5ac71d7224b4ec3fe81d508eb23d4e8a52')
receipt=pin(A/'observation.json','19a5d96a179ffb895e6087d973bd49d276ecbb9f6971372490624803ba653c47')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-four-fields-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='c5ddece62b62ca67f8a1d3d5fc9e33cb3e493d445593aa27dad5df2e149194c7'
p=D/'reviews/ordinary14-direct-first-root-model-draft-independent'
pin(p/'check.py','8b37d7c3a5150a692ff6724bdb4b3f6b9ef4323c86c00ecee7464f9be636db9a')
pin(p/'result.json','d778572f31087ae910bf979a9570c9b42c8bc8c3f89ecdf364607533e7856616')
for f in ('(hz : InternalZero (P88FourSquare.graph p).output v)',
 '(eval (P88FourSquare.graph p).aux v-1)',
 '(eval (P88FourSquare.graph p).gap v) 0=0',
 'fiveSquares_eq_zero_iff _ _ _ _ _','exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩'):
 assert f in s,f
n=0
for fs in itertools.product(range(-2,3),repeat=4):
 if sum(x*x for x in fs)==0:assert all(x==0 for x in fs);n+=1
assert n==1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'13-parent own-zero four-field source review; no Lean','bounded_zero_cases':n,'prior_square_review':'pinned, not rerun'},sort_keys=True,indent=2))
