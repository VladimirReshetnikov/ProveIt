#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-ipra-endpoint-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'f24154e06016664e649f3ae6cadc297c1d4c8574129d0ccc874ecf759f45315f',A/'Root74Endpoint.lean':'1259b42c95c6601a323dcbdc5df6bb74220cfc91be8c7dd175a693aaf1728bd5',A/'check_source.py':'5f31c14a050a6905f5ba615f4c60e944394dff4a685d8aca93c86163189e5e04',A/'observation.json':'895f826fe9aaad2bf10990f5ad78170901cd5155e3bec73cfcfe63b1548fb1e3',D/'research/ordinary14-root74-positive-bridge-draft/Root74PositiveBridge.lean':'f54228acca9fd8db59d25bdd65b3cf4910fb4bd8c7395524c2c4803fdc047e90',D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean':'df2b30357f7c236c72fa70f4e6de558c3a435d74be97e13f6c52a8b230886ce9',D/'research/ordinary14-root78-ipra-endpoint-draft/Root78Endpoint.lean':'99c2f87ba53467a402e80bc33b4242374c7f6695a5607c10a9e7fa1c3c06303c'}
tail=b'\nIndependent source review: [root74 iPRA adapter](../../reviews/ordinary14-root74-ipra-endpoint-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='310eeeaeb057ff492f657c55c0e10711caea017c4fe5a619268afb8929b56d98'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
s=(A/'Root74Endpoint.lean').read_text();old=(D/'research/ordinary14-root78-ipra-endpoint-draft/Root78Endpoint.lean').read_text();api=(D/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean').read_text();bridge=(D/'research/ordinary14-root74-positive-bridge-draft/Root74PositiveBridge.lean').read_text()
def theorem_block(x):return x[x.index('theorem native_equivalence :'):x.index('#print axioms native_equivalence')]
assert theorem_block(s).replace('Root74PositiveBridgeDraft','Root78PositiveBridgeDraft')==theorem_block(old)
assert 'def expression : Expr (Fin 14)' in bridge and 'theorem positiveBridge : PositiveModelBridge expression' in bridge
for t in ('theorem native_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)', 'theorem standard_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)', 'theorem reference_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e)', '∼IPRAOrderErasure.erase (mappedNativeRefutation embedding)'):
 assert t in api,t
assert s.count('positiveShift Root74PositiveBridgeDraft.expression')==3
assert s.count('∼mappedNativeRefutation embedding')==2
assert s.count('∼IPRAOrderErasure.erase (mappedNativeRefutation embedding)')==1
assert s.count('_of_positive _ Root74PositiveBridgeDraft.positiveBridge')==3
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'observation.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'source-interface review only; positive bridge separately unreviewed, no Lean/iPRA theorem','theorem_block_matches_root78_after_namespace_substitution':True,'positive_shift_applications':3,'mapped_refutation_rhs_applications':3,'author_receipt_replayed':True,'reviewed_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
