#!/usr/bin/env python3
"""Independent 88 own-zero main norm source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-main-norm-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'MainNorm88.lean','9c6dd4deef3785fb2acd460448ffa9c1ab77b8247d0e74fd0087df054ec74715').decode()
pin(A/'check_source.py','a7351fcd3bb529dfce0068f40c1568d6628a92d5a28be917f14a8853d6e62298')
receipt=pin(A/'observation.json','6976e4917dd1b11f0ba7d6fbf6bcabd6f8b3a5cce3b8186dfd14e79609688fe1')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-main-norm-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='4628d0865d7e595b42f7e4f204d89276d2e5f760a674c139bd1cb025b47b01ab'
for name,ch,rh in (
 ('ordinary14-88-first-quotient-draft-independent','13f050ff276242ff251957aac4d6b5650c48e17a3007a97ced2b83a90fac577f','4bc220c6bb64678ae0e25c479042a5c9a7cb26f2f2f6e300ad1b910dd2181fc7'),
 ('ordinary14-aux-ring-norm-extraction-draft-independent','2c1f4001512c55630f2cd54bdcc1aaf3acb3ddd9d397a07e9255200415012131','aedd28513b914650aa27638b9eb4469c5ff063981f6b2a1b4183cd37c22da28c')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hz : InternalZero (P88QuotientGuarded.graph p).output v)',
 'FirstQuotient88Draft.forward_zero p v hz','have hU : 0<U beta u',
 '(FourFields87Draft.fields_of_zero p u hz\').2.1',
 'MainBalance87Draft.main_eval p beta u hport',
 'root_of_scaled_ring_square (U beta u) (1+Delta u*c u*c u)',
 'simpa [u,PositiveMap88To87Draft.forward,Delta,a,c,k] using hroot'):
 assert f in s,f
n=0
for U in range(1,9):
 for root in range(0,9):
  for sign in (-1,1):
   Z=sign*U*root;assert Z*Z==U*U*root*root;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 own-zero natural main norm source review; no Lean','signed_scale_controls':n,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
