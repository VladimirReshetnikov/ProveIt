#!/usr/bin/env python3
"""Independent compact 78↔88 source composition review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-78-88-compact-model-composition-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Compact78To88.lean','84df038dac5927454e4387108c4f1e1c940fd7c1f4cd868741ce17123fd38d12').decode()
pin(A/'check_source.py','ab0f5835b73c32ba7ce06744eef64779dc841cb4ccfd900f72f21c808a84c7b4')
receipt=pin(A/'observation.json','45150e8576f1341878bbcd230cc70efd4bbc03384ad7b6699e30c0a9aca7c985')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-78-88-compact-model-composition-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='ebc7493ff8be1397fa41b6abc888035e71f7109c7a3552023276da9695716fda'
for name,ch,rh in (
 ('ordinary14-78-87-compact-model-composition-draft-independent','cea82e1dc03d99c4f16e76a83aad2f9608d59ef731ecf32f0e9bd3499250eb21','88a34fc461883205f2596075d762c7d703e0cab24ae605394e3258e1faff9233'),
 ('ordinary14-87-88-compact-model-equivalence-draft-independent','667f94dd9b012c2bb262397f0bf67aafdc1f315b52ec904b545262610f1479fc','3c3ad49b41b1fb91bb5f38910642e0c6f4d6da576cc987af7a17b6787df1d24d')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('theorem positive_zero_iff (K : ℕ)','ports CompactFixedBeta.betaNat K lowNat highNat',
 'P78AuxRoot.graph (fun j => (p j : ℤ))','P88QuotientGuarded.graph (fun j => (p j : ℤ))',
 '(Compact78To87Draft.positive_zero_iff K).trans','(CompactEquivalence8788Draft.positive_zero_iff K)'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'compact 78/88 symbolic source composition; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
