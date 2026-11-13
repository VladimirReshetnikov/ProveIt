#!/usr/bin/env python3
"""Independent quotient-88 positive-model bridge source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-quotient88-positive-bridge-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Quotient88PositiveBridge.lean','70c4de06af25faa46a647331605f01be386577b0f8d616beb256312a2b1bc4ac').decode()
pin(A/'check_source.py','31a0464cae2d44867ce5394089194dbf4a6246931b85e695a3342235797aa348')
receipt=pin(A/'observation.json','f37dd374e6a8a9a8dabf89a9216cbacc7a99e838720ab2af5adb301ef391c0e8')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-quotient88-positive-bridge-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='d750917abc4b91316cbe06d6e377817695c8ad63731ecc8b8cc8c04a8eed64f3'
p=D/'reviews/ordinary13-14-parent-88-model-equivalence-draft-independent'
pin(p/'check.py','d2644d9c454c9c2ccee8727cb805a3c8b770f65d5dcea41ff28c8c101c7880f0')
pin(p/'result.json','af8891deeb0b718a4adea57001cc92a2429054ec5f0930da3ee7fc5479fa1923')
pin(D/'research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean','1fb9d7a6d1b906c87877c3146787c5fea5558f2473aac029b7be702763df7192')
sym=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46').decode()
bridge=pin(D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean','1476d90741c9cae95b164c4de25dcbdf43399347eee97b9031684f9b1a916ce1').decode()
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in sym
assert 'def PositiveModelBridge {n : ℕ} (e : Expr (Fin n)) : Prop :=' in bridge
assert '∃ time : V, first (ArithmeticMachineRun215.run time) = 0' in bridge
for f in ('ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat',
 'Parent88EquivalenceDraft.positive_zero_iff (V:=V) p hb.1',
 'InternalZero P88FourSquareModel.expression v','InternalZero expression w',
 'hpair.symm.trans (P88FourSquareModel.positiveBridge V)'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'symbolic positive-model bridge source review; no Lean or physical binding','prior_model_iff_review':'pinned, not rerun'},sort_keys=True,indent=2))
