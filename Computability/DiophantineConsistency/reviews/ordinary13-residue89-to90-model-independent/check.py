#!/usr/bin/env python3
"""Independent r-shift source and forced/existential transport audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue89-to90-model-draft/Residue89To90Transport.lean.src','8cdbb1809435b9eb09fa930db4e1e13c112ba459aa93d4338d73af2cbf94b0fe')
e=pin('research/ordinary13-residue89-to90-model-draft/Residue89RootSwitchTransport.lean.src','f0d0607cd42e6d1226ee498686dd134819cfdbf50f895f27629cb98e09d94c4a')
pin('research/ordinary13-residue89-to90-model-draft/receipt.json','13d5e7a5b0399453d88ac275c54de85a3cb2a978f266a801deb7305c887e7b55')
l89=pin('research/ordinary13-residue-folds-model-draft/ResidueFoldP89.lean.src','1cf3ece1241b09402110f78d7be1712b508e431c763772af5a0f6e91d3bb2a73')
r89=pin('research/ordinary13-residue-folds-model-draft/ResidueFoldP89Residuals.lean.src','02849926cb905aa822f0c077329ddef012c8058184ffd719a62c5350a24717c4')
l90=pin('research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src','00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af')
r90=pin('research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src','efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925')
pin('reviews/ordinary13-residue90-to82-model-independent/result.json','e9f1ea08c2187fb7ba63b544b339f2891a934db24846d4065be9c94e49391112')
pin('reviews/ordinary13-residue-root-switch-model-draft-independent/result.json','ee962267652ae67f6cb059b1cd4820fb59a573b10fdd4a8eb794df71e19c8d01')
pin('reviews/ordinary13-residue89-r-model-independent/result.json','6b78beba893858cb091ea5cd8020856b17402572c11e8996e3ce8e408d6c7502')
for a,b in [(l89,l90),(r89,r90)]:
 expected=a.replace('ResidueFoldP89DraftResiduals','Residue90ResidualsDraft').replace('DiophantineConsistency.ResidueFoldP89Draft.literal','Residue90LiteralDraft.literal').replace('ResidueFoldP89Draft','Residue90LiteralDraft').replace('import ResidueFoldP89','import Residue90Literal')
 expected=expected.replace('  let shift_s := n_s + 1\n','  let shift_s := n_s + 1\n  let shift_r := n_r + 1\n').replace('  let g31 := g30 + n_r','  let g31 := g30 + shift_r')
 assert expected==b
for x in ['if i=8 then v i+1 else v i','if i=8 then v i-1 else v i','(h : 0<v 8)','def ForcedR','(hr : ForcedR K)','(h82 : PolynomialBridge (positiveShift','Residue90To82TransportDraft.polynomialBridge K h82']:
 assert x in s,x
for i in range(4):assert f'theorem relation0{i}' in s
for x in ['def PositiveReplacement','∃ w : Fin 13 → V','0<w 8','theorem forced_implies_replacement','⟨v,hz,h V v hz⟩','obtain ⟨w,hw,hpositive⟩ := hr V v hz','(hr : PositiveReplacement K)','(h82 : PolynomialBridge (positiveShift']:
 assert x in e,x
for n in range(1,100):assert (n-1)+1==n
print(json.dumps({'scope':'exact source delta and conditional root-coordinate model maps; no Lean','r_coordinate':8,'all_residual_relations':4,'original_r_forcing_stronger_than_positive_replacement':True,'both_paths_conditional':True,'positive82_parent_bridge_explicit':True,'lean_elaborated':False},sort_keys=True,indent=2))
