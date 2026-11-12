#!/usr/bin/env python3
"""Independent symbolic root-78 positive bridge source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-root78-positive-bridge-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Root78PositiveBridge.lean','d9cd05f4e1aa64ddf4d4f800ba51c3a9774558e95b2709950d115acb3b9b166a').decode()
pin(A/'check_source.py','3b7e10389d9456e7eb36494d80c3150eb1fc5720474405266d8c33c8a8b8eb75')
receipt=pin(A/'observation.json','4a5b758bb5f404f7269ed6986569093224d57609328b6114752376684386a2ba')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-root78-positive-bridge-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='c24386af77b567d425a8ad78d0eb79939420667dbc9b7d5c0c04c055162e8c43'
for name,ch,rh in (
 ('ordinary14-78-88-compact-model-composition-draft-independent','51515996c63f45166e6b64adeaffbebe89c67f6e04483a6dc31dad5d5e7991e9','4ffdf744788e19e7a3408e2b435e8ea10c091b4e3f8035b092e2c90bcad15508'),
 ('ordinary14-quotient88-positive-bridge-draft-independent','3489d54c93c04a915daccfcbbc01c85294c2cbba6d861455898d57a5512e081e','bd099285c2271f5670513816e5f8c3dd9f4bb0489a23904ea66697756afbc6e0')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(P78AuxRoot.graph CompactSymbolicModelIff.p).output',
 'Compact78To88Draft.positive_zero_iff (V:=V) (paramKernel rho)',
 'InternalZero expression v','InternalZero Quotient88PositiveBridgeDraft.expression w',
 'hpair.trans (Quotient88PositiveBridgeDraft.positiveBridge V)'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'symbolic root-78 positive-model bridge source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
