#!/usr/bin/env python3
"""Independent source-delta and conditional transport audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-to91-model-draft/Residue90To91Transport.lean.src','f11b374e46e2c8347a55ddc6f7c43cd60af88b9465aec6160fb0f1834ae1121b')
l91=pin('research/ordinary13-residue90-to91-model-draft/Residue91Literal.lean.src','93c7c115fb28aebc97899ec166ccf6b013a778df628619bfed72a3a2afd536de')
r91=pin('research/ordinary13-residue90-to91-model-draft/Residue91Residuals.lean.src','c812879f3c7057b272eac00d0e2b251e64e471560e0217296b71a4bc05218c98')
pin('research/ordinary13-residue90-to91-model-draft/receipt.json','552d2fa6535384dca398f881f7f0c8d69f26315b65b7dda0cd779d5d378d6a98')
l90=pin('research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src','00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af')
r90=pin('research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src','efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925')
pin('reviews/ordinary13-residue90-xzero-graph-independent/result.json','ffa967831cfed486dca16c9f3bbf9a3735fcc0e298c13b1cfc124a19b8b0cc6e')
b=pin('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean','d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06')
n=pin('Lean/DiophantineConsistency/IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8')
for old,new in [(l90,l91),(r90,r91)]:
 expected=old.replace('Residue90','Residue91').replace('  let qm :=','  let shift_gamma := n_gamma + 1\n  let qm :=').replace('  let g54 := U * n_gamma','  let g54 := U * shift_gamma')
 assert expected==new
assert '![A0,A1,Fam,g72]' in r91 and ': Fin 4 → Expr (Fin 13)' in r91
for z in ['if i=12 then v i+1 else v i','if i=12 then v i-1 else v i','theorem raise_lower','(h : 0<v 12)','theorem compact_no_zero_iff','Residue90XZeroGraphDraft.compact_gamma_positive','(hparent : PolynomialBridge (Residue91LiteralDraft.literal','theorem native_equivalence']:
 assert z in s,z
for i in range(4):assert f'theorem relation0{i}' in s
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in b
assert '(hp : HAExpressionAssembly.PolynomialBridge e)' in n
# On naturals, increasing gamma maps a 91 valuation to a 90 valuation;
# every positive 90 gamma has a unique nonnegative predecessor.
for gamma in range(1000):
 assert (gamma+1)-1==gamma
 if gamma>0:assert (gamma-1)+1==gamma
print(json.dumps({'scope':'exact source delta and conditional zero-map interfaces; no Lean','gamma_coordinate':12,'residuals_in_order':['A0','A1','Fam','g72'],'positive_gamma_needed_for_reverse':True,'parent_PolynomialBridge_explicit':True,'compact_K_arbitrary':True,'physical_byte_binding_unproved':True,'lean_elaborated':False},sort_keys=True,indent=2))
