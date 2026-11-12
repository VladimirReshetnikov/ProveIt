#!/usr/bin/env python3
"""Independent 88 own-zero first-root-gap source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-first-root-gap-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstRootGap88.lean','5b3ee55a4fe3684c8094867903d4a533a74ca80dad4f24b8733b65ae1a3837c4').decode()
pin(A/'check_source.py','b6089d024a38d65473c7ac1eddf5f4ea9be88faeb5a42f435787c7a09e1d77e9')
receipt=pin(A/'observation.json','994b8fb27840e4d7af659c079b8fb1a37c1cf4c0c23c5b972f84a571ac24c3fe')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-first-root-gap-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='29bc65e2565c70736d262160da5fdc28fcbb8c4347d8415f84b3221c0f514bd3'
for name,ch,rh in (
 ('ordinary14-first-root-gap-draft-independent','474f09cedc235fc057d1fd1867037f065942c0ecf7793794b7e6197349778aba','2a9afa96fb14ff99f464e6df6aac6e919b9eb162324974fff66a0159a8db4acb'),
 ('ordinary14-88-main-norm-draft-independent','e57621bc972b1f67d614b5f92a9efcfd748a7e0ed4f3b10f744caca1cf58e206','7a0c2d2db9cf9f45b824bbfdebb1e3cb468e0b8a3a3a24060dd7201f8b8bfcaf'),
 ('ordinary14-88-first-quotient-draft-independent','13f050ff276242ff251957aac4d6b5650c48e17a3007a97ced2b83a90fac577f','4bc220c6bb64678ae0e25c479042a5c9a7cb26f2f2f6e300ad1b910dd2181fc7')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('FirstQuotient88Draft.quotient_and_root p beta v hbeta hJ hY hport hz',
 'MainNorm88Draft.main_norm p beta v hbeta hJ hY hport hz',
 'FirstMainLargeKDraft.first_main_large_k',
 'have hsm : s≤m := le_trans hsY hYm',
 'FirstRootGapDraft.root_gt_linear m (k v) tau s hm hsm hk'):
 assert f in s,f
n=0
for q in range(1,8):
 for X in range(1,8):
  for s0 in range(1,8):
   Y=q**3*s0;m=X*Y*Y
   assert s0<=Y<=m;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 own-zero first-root gap source review; no Lean','finite_quotient_cases':n,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
