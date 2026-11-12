#!/usr/bin/env python3
"""Independent 87↔88 model source wrapper review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-88-model-equivalence-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','7f7569a052ba3a2f922a7d169f065af395e48dacf194884aa75a17a88d54e5c5')
s=pin(A/'ModelEquivalence8788.lean','edc74a0786634eb0db4921ee19c098e34f194b7b86ec92cad2071dfff45bd076').decode()
pin(A/'check_source.py','902b03133c2831a42f6313348e89dbb39fc5b232efc24908dcd57b4032b37f19')
receipt=pin(A/'observation.json','07f567a4988fc227a6cddc67d3ffd9fe03137b954b68defb0fb3387131871de9')
for name,ch,rh in (
 ('ordinary14-87-to-88-model-map-draft-independent','ee3d1fce93301b4b17f9e91031950c6e84de08f8ee89d768e9c5ee5e0404d282','cb514d21f4198bcc72d3048eabc17ff438dc377e2cb9a3126eedc8eb284909a4'),
 ('ordinary14-88-to-87-positive-map-draft-independent','b2d19316ffe6b73c00f7e931b330cfc7de6ac1fccd1e9cdd158c6a9cb1140198','0f74400f0f53eca7e96a0b45c76ad596910d3f7206d308ff806fdf86519ea5ff')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hbeta : 0<beta) (hbeta46 : 46≤beta)',
 '(hMC : MC<beta) (hMF : MF<2*beta)',
 'P87ShiftedGuard.graph p','P88QuotientGuarded.graph p',
 'ModelMap87To88Draft.positive_map p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz',
 'PositiveMap88To87Draft.positive_map p v hv hz'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'87/88 model iff source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
