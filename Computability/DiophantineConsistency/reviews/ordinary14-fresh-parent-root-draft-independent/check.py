#!/usr/bin/env python3
"""Independent positive fresh-root source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-fresh-parent-root-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FreshParentRoot.lean','36e1cd292603e369bb88bc1f999877cefaaadb859d93e8efc6360a3c5c4676c6').decode()
pin(A/'check_source.py','c9464a3b5117d41025655725c518ac8b1afa489e52acd095953703c63990bd70')
receipt=pin(A/'observation.json','8fcc1330d031db102c49fa9936feab0883a7000fdf62c48c64f4433499d54553')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-fresh-parent-root-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='fcec8b14db90b224622ea82375d5a7ca5f54b02e4f6933c55a4955738d9efae9'
p=D/'reviews/ordinary14-first-root-gap-draft-independent'
pin(p/'check.py','474f09cedc235fc057d1fd1867037f065942c0ecf7793794b7e6197349778aba')
pin(p/'result.json','2a9afa96fb14ff99f464e6df6aac6e919b9eb162324974fff66a0159a8db4acb')
for f in ('(hb : 0<b) (ht : 0<t)','(hgap : m*k+s<tau)',
 'have hbt1 : 1≤b*t','have hk : k≤k*(b*t)',
 '⟨B-A,tsub_pos_of_lt hAB','tsub_add_cancel_of_le (le_of_lt hAB)'):
 assert f in s,f
n=0
for m in range(7):
 for k in range(7):
  for s0 in range(7):
   tau=m*k+s0+1
   for b in range(1,8):
    for t in range(1,8):
     A0=m*k+k+s0;B=k*b*t+t+tau;root=B-A0
     assert root>0 and root+A0==B;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'positive fresh-parent-root fact source review; no Lean','finite_controls':n,'prior_gap_review':'pinned, not rerun'},sort_keys=True,indent=2))
