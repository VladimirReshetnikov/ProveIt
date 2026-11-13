#!/usr/bin/env python3
"""Independent 87→86 model-map source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-to-86-model-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ModelMap87To86.lean','3f602fc37d8e6be21d02dff60abd70948cc3f8b20266c7428e87d069d5d0546f').decode()
pin(A/'check_source.py','1bd3ca69e5724804f0ac7eb2a3e4e3da1aac7534b116853dbbffd4eb217f1fbc')
receipt=pin(A/'observation.json','ccb4d2760ad8b12e4f6929d0baf6d57af480511c96a85e42cd2bfe26b1fa41c0')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-to-86-model-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='93f629d95bc9ae233e08da04b48aa0f152a75dbb30e8303a0334d4ca4164d90d'
for f in ('(hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'PowerRecovery87Draft.power p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz',
 'Divides3X87Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'MersenneGuard87Draft.strict_of_power p beta K t R v hbeta ht hradix hport hK hv hX h3 hz',
 'GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'ConditionalMap87To86Draft.positive_map p beta K v hport hK hv hgap hstrict hz'):
 assert f in s,f
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-power-recovery-draft-independent','ordinary14-87-mersenne-guard-draft-independent','ordinary14-87-to-86-conditional-map-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87-to-86 model-map source composition; no Lean or provider closure','component_reviews':3},sort_keys=True,indent=2))
