#!/usr/bin/env python3
"""Independent 87→88 model-map source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-to-88-model-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ModelMap87To88.lean','4f86f9249e36cbf656cc0ddc4480028bf9f8b2e99e1b2070d3c24a9d9c6ddefb').decode()
pin(A/'check_source.py','08c29e3e7f868c827f439acf5b4502dbf74edd36eabb76b1f5df8c96bdba7025')
receipt=pin(A/'observation.json','d7883a49d6de42a4c5242f43c6e49a3d8e6744246bffc56761f0042f0dc55d57')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-to-88-model-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='92c4c0525316261b1adb25c4c0038a734f98d7cf0a3294fca3ddfbf75d88f848'
for name,ch,rh in (
 ('ordinary14-87-omega-gt-f-draft-independent','4b9cf83565f39b7d178ae4f344ca3721322ce9124a1962b75cac5b35af901cf7','df459b1fdd2fdddac5b833e7a01c8f53cbbe68a16589ddc41d967ce32da11ac8'),
 ('ordinary14-87-to-88-conditional-map-draft-independent','9e53943541bb8beb161113d4be042714911c2ce7718bb35d9abd210dbec3613e','e184c5d0629c0e53e447e15d6d754c91a6c6118035ad3a6c775d159dc7aa8240')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hbeta : 0<beta) (hbeta46 : 46≤beta)',
 '(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'OmegaGtF87Draft.omega_gt_F p beta K MC MF v',
 'hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz',
 'ConditionalMap87To88Draft.positive_map p v hv hstrict hz'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'87-to-88 calibrated source map review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
