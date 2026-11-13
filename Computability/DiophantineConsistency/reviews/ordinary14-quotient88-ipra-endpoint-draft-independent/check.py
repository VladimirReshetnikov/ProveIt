#!/usr/bin/env python3
"""Independent quotient-88 iPRA source adapter review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-quotient88-ipra-endpoint-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Quotient88Endpoint.lean','d06f6a29834653b130c2886059475e2903a48a3d7f1e6cdceb9752ee5d8925e3').decode()
pin(A/'check_source.py','9a7eaafd9118835debd4b16719716afa2c902fb64fbc803f5f435b54791bc615')
receipt=pin(A/'observation.json','3ae2727b98576cc0842983da5e3ec38a11797567d74c6eb3273c24d6770364c1')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-quotient88-ipra-endpoint-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='b884b9f366c3aa2741972ea2f00281a4025466061c20abc0c308603e9bbc6280'
p=D/'reviews/ordinary14-quotient88-positive-bridge-draft-independent'
pin(p/'check.py','3489d54c93c04a915daccfcbbc01c85294c2cbba6d861455898d57a5512e081e')
pin(p/'result.json','bd099285c2271f5670513816e5f8c3dd9f4bb0489a23904ea66697756afbc6e0')
ad=pin(D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean','df2b30357f7c236c72fa70f4e6de558c3a435d74be97e13f6c52a8b230886ce9').decode()
for name in ('native_of_positive','standard_of_positive','reference_of_positive'):
 assert f'theorem {name} {{n : ℕ}} (e : Expr (Fin n)) (h : PositiveModelBridge e)' in ad
 assert f'{name} _ Quotient88PositiveBridgeDraft.positiveBridge' in s
for f in ('IPRAExpressionNative.nativeNoZero (positiveShift Quotient88PositiveBridgeDraft.expression)',
 '∼mappedNativeRefutation embedding','IPRAOrderErasure.erase (mappedNativeRefutation embedding)',
 '#print axioms native_equivalence','#print axioms standard_equivalence','#print axioms reference_equivalence'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'symbolic iPRA adapter source review; no Lean or axiom replay','prior_bridge_review':'pinned, not rerun'},sort_keys=True,indent=2))
