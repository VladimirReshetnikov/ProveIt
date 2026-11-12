#!/usr/bin/env python3
"""Independent 88-to-parent first residual source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-parent-first-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentFirst88.lean','6d0bcc465ac56a62e85b5ce895a6bcdee9180d6c8c565f803304e0e094df588f').decode()
pin(A/'check_source.py','6a6e65b3871579ed2932ba99c49c5dace036b82e61247e060c33f2cb46619d00')
receipt=pin(A/'observation.json','0ef6c02efde4ccfac84c5fc9bfe3d1f8fa6a8183be372c644eeb17d112e1e02a')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-parent-first-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='ae9610d48f1d92f5c697ffff6f0e3db4cb142ce8c403c7e0ae053b181fd65773'
for name,ch,rh in (
 ('ordinary14-88-parent-ring-client-draft-independent','880c9b6e5b89a922d05f35414367af24a5e4d1dea0667479ce6fd7add019e43a','ee5684d0c6d91a32eb601dc8370b1195201e716a29cfeca7c8a5593ab5a4a848'),
 ('ordinary14-88-guard-draft-independent','11b01dfb20f0c90bbf0c28c638cf7a95bc0e02ed6814dc65d45cffd8af0d6c90','35cda6ae4546078790eee91db89cd5933fcca8140d9589de7539ce303602d03e')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hz : InternalZero (P88QuotientGuarded.graph p).output v)',
 '(hY : v 7=Q beta v*s) (htau : tau*tau=radicand v)',
 'Guard88Draft.bt_of_zero p beta v hport hz','Ring88ToParentDraft.first_cut',
 'rw [hbt,Ring88ToParentDraft.scale,hcut,hdelta,←ht] at hf'):
 assert f in s,f
n=0
for q in range(2,7):
 for X in range(1,4):
  for s0 in range(1,4):
   Y=q**3*s0;m=X*Y*Y;P=2*m+1;delta=P*P-1;tau,y=1,0
   for j in range(2):tau,y=P*tau+delta*y,tau+P*y
   k=2*y;ell=m*k;M=q**3*(q-1)
   for t in range(1,4):
    b=q-1;r0=k*b*t+t+tau-ell-k-s0
    assert r0+ell+k+s0==k*b*t+t+tau
    Z=M*(ell+k+r0-k*b*t)+Y*b-q**3*b*t
    assert tau*tau==1+m*(m+1)*k*k and Z*Z==M*M*tau*tau;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 projected parent first-residual source review; no Lean','finite_first_field_controls':n,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
