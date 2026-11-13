#!/usr/bin/env python3
"""Independent parent-to-88 first residual source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-to-88-first-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentTo88First.lean','9b7714202cc8957fe4bfdc3eab2989b7206dd8d3d861229beb5d5979eb41c38a').decode()
pin(A/'check_source.py','2d616b493a2f85856d3f32659d78149df49eb7e861cc2887deaa399db8043009')
receipt=pin(A/'observation.json','5c107d4252c86ec45e64aff7ed30dcb30c2563b817884c8f6a48dc4e52f92bcc')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-to-88-first-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='9e2ea920c599942df0b9ad84039d8df41592ce8e93f6341c168e1b1d1645cfce'
for name,ch,rh in (
 ('ordinary13-parent-to-88-ring-client-draft-independent','a9da9ee6a83c8e427fce9bc1ffd31ffbae0d90838621e73ec90abd7efd2fa3b6','93c66ee81872d59375690e60fb40f02ac1582363bde2e0c02ff11e051cca1996'),
 ('ordinary14-parent-to-88-first-cut-draft-independent','608ca58009404a3be7586a38c0867e7da63e0de6b9c6f8ed7660f1ed0b7ccc76','6c6a51f850d210f1c64b12fed05af2089e8803f216fb86937c69f1da70020b05')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hY : v 7=Q p v*s) (htau : tau*tau=D v)',
 'P72Root.cast_port p 0','ParentTo88FirstCutDraft.fresh_first_cut',
 'rw [←hsigma] at hcut','RingParentTo88Draft.first_eval pi z',
 'rw [Ring88ToParentDraft.scale,hcut,hD,←ht] at hf','rw [hf]'):
 assert f in s,f
assert 'from hsigma,Ring88ToParentDraft.scale' not in s
n=0
for q in range(2,7):
 b=q-1;Q=q**3;M=Q*b
 for X in range(1,4):
  for s0 in range(1,4):
   Y=Q*s0;m=X*Y*Y;P=2*m+1;delta=P*P-1;tau,y=1,0
   for j in range(2):tau,y=P*tau+delta*y,tau+P*y
   k=2*y;ell=m*k;sigma=ell+k+s0+tau
   Z=M*(ell+k-sigma)+Y*b
   assert Z==-M*tau and Z*Z==M*M*(1+ell*(ell+k));n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'parent-to-88 first residual source review; no Lean','finite_first_field_controls':n,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
