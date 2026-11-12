#!/usr/bin/env python3
"""Independent root-78 iPRA adapter source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-root78-ipra-endpoint-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','b522c906da477bf8591c2624c408a40663f762bdd665d67a1c419ff060f6b86f')
s=pin(A/'Root78Endpoint.lean','99c2f87ba53467a402e80bc33b4242374c7f6695a5607c10a9e7fa1c3c06303c').decode()
pin(A/'check_source.py','0258d69c2e6230e3c9e63dbea53dd2c07623c299a02ad08aa32c366c6496db9e')
receipt=pin(A/'observation.json','df7c15531a899857b5e2e7d6a18fe30aa83bd491fe0436ddeb8361cdc488fa3a')
pin(D/'research/ordinary14-root78-positive-bridge-draft/Root78PositiveBridge.lean','d9cd05f4e1aa64ddf4d4f800ba51c3a9774558e95b2709950d115acb3b9b166a')
ad=pin(D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean','df2b30357f7c236c72fa70f4e6de558c3a435d74be97e13f6c52a8b230886ce9').decode()
for name in ('native_of_positive','standard_of_positive','reference_of_positive'):
 assert f'theorem {name} {{n : ℕ}} (e : Expr (Fin n)) (h : PositiveModelBridge e)' in ad
 assert f'{name} _ Root78PositiveBridgeDraft.positiveBridge' in s
for f in ('IPRAExpressionNative.nativeNoZero (positiveShift Root78PositiveBridgeDraft.expression)',
 '∼mappedNativeRefutation embedding','IPRAOrderErasure.erase (mappedNativeRefutation embedding)',
 '#print axioms native_equivalence','#print axioms standard_equivalence','#print axioms reference_equivalence'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'symbolic root-78 iPRA adapter source review; no Lean or axiom replay','bridge_source':'pinned, not independently rerun'},sort_keys=True,indent=2))
