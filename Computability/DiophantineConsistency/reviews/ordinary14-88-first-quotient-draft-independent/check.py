#!/usr/bin/env python3
"""Independent 88 first quotient own-zero source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-first-quotient-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstQuotient88.lean','2c3eaabd413869251c6726a4f2c910700ff0ac1e35c2551c65ea2133c99fba1c').decode()
pin(A/'check_source.py','d04fb1e275a516321dcf5dbea5859310c26c19d1d7fdafb3b0c1564cacfcc778')
receipt=pin(A/'observation.json','4edad8adf18ca3c1ec1f0cc9e4a92d304ffe99961a1126daf55d4c7d60fe54ee')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-first-quotient-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='ab2ac27afe7032ca599e3d6d28f910bbf71e69eff36f6f0b3760e7509effbaed'
for name,ch,rh in (
 ('ordinary14-88-87-ring-client-draft-independent','8c9d57162551423da72a8ad2080a841bc8c49a85cb3e245979bed19ffea4d265','9650b27c43ad2fcee4ab4abb20b3bfe7d48bcbe77b3e35cf52836a7465cf299f'),
 ('ordinary14-87-first-quotient-draft-independent','798f30ee663c490d354469fa1cf95e683b7217b703a717a457bd3aeac2da2a8b','cb742e8f9f705b58733489cab18d43475c5c503b5e4e9da10ecf9be5d534e04d')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hz : InternalZero (P88QuotientGuarded.graph p).output v)',
 'Ring88To87Draft.output_eval p (fun j => ι (v j))',
 'rw [←PositiveMap88To87Draft.cast_forward v] at h',
 '(hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)',
 'FirstQuotient87Draft.quotient_and_root p beta u hbeta hJ\' hY\' hport hz\'',
 'simpa [u,PositiveMap88To87Draft.forward,Q,q,radicand,firstP,ell,k] using h'):
 assert f in s,f
for F in range(6):
 for t in range(6):
  v=list(range(14));v[1]=F;v[13]=t;u=v.copy();u[13]=t+F
  assert all(u[j]==v[j] for j in range(13))
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 own-zero first quotient source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
