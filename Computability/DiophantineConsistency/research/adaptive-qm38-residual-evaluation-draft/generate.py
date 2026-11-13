#!/usr/bin/env python3
"""Generate inert residual and evaluation proofs from pinned source data."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
child=json.loads(pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'))
oldsrc=pin(D/'Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece')
old=json.loads(pin(D/'research/adaptive-square-sums40-quotient-quartic/candidate.json','fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d'))
literal=pin(D/'research/adaptive-qm38-conditional-model-draft/AdaptiveQM38Literal.lean.src','f033af128e5ca4c7a5a1473e6370fc385d0354b110067ae84e168eed6643a44d')
pin(D/'research/adaptive-qm38-conditional-model-draft/AdaptiveQM38ConditionalTransfer.lean.src','104e56bcbc2ef2c922864c443b607fdc69ea048a8546d7c1d69340c6e7c7b588')
pin(D/'research/adaptive-qm38-conditional-model-draft/AdaptiveQM38EvaluationCut.lean.src','08707aa597d45389ab038fcda534d342ec4487913da52832ea441241fa9fee0b')
start=oldsrc.index('def residuals (p : Fin 4 → ℤ) : Fin 31 → Expr (Fin 40) :=');end=oldsrc.index('\ndef sum (p : Fin 4 → ℤ)',start)
vectors=re.findall(r'  !\[([^\n]+)\]',oldsrc[start:end]);assert len(vectors)==1
parentResid=vectors[0].split(',');assert len(parentResid)==31 and parentResid[20]=='ellProductDifference' and parentResid[24]=='deltaProductDifference'
retained=[(i,n) for i,n in enumerate(parentResid) if i not in (20,24)];assert len(retained)==29
res=[n for _,n in retained];assert set(res)<={r[0] for r in child['source']}
assert child['operations']==len(child['source'])==160 and old['operations']==len(old['source'])==166
# Syntactic DAG identity for the displayed child sum; no commutative rewrite.
node={x:('leaf',x) for x in child['witnesses']+child['fixed_numerals']}
def arg(x):return ('integer',x) if type(x)==int else node[x]
for n,o,a,b in child['source']:node[n]=(o,arg(a),arg(b))
sums=None
for n in res:
 square=('*',node[n],node[n]);sums=square if sums is None else ('+',sums,square)
assert sums==node[child['output']]
# Literal row block and input binders are copied exactly from the pinned draft.
start=literal.index('  let J : Expr (Fin 38) := .var 0');end=literal.index('\n  -- END GENERATED ROWS',start)
body=literal[start:end].replace('  -- BEGIN GENERATED ROWS\n','')
sumExpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(29))
R='''import AdaptiveQM38Literal

/-! Source-only named 29 residual vector; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM38ResidualsDraft
open AdaptiveEquationSyntax2011

def residuals (p : Fin 4 → ℤ) : Fin 29 → Expr (Fin 38) :=
'''+body+'\n  !['+','.join(res)+''']

def sum (p : Fin 4 → ℤ) : Expr (Fin 38) := '''+sumExpr+'''

theorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AdaptiveQM38LiteralDraft.literal p := by rfl
end DiophantineConsistency.AdaptiveQM38ResidualsDraft
#print axioms DiophantineConsistency.AdaptiveQM38ResidualsDraft.sum_eq_literal
'''
(P/'AdaptiveQM38Residuals.lean.src').write_text(R)
header='''import AdaptiveQM38Residuals
import AdaptiveQM38EvaluationCut
import Mathlib.Tactic.Ring

/-! Candidate residual-by-residual proof of the difference-ring identity.
This and all imported drafts are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM38ResidualEvaluationDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AdaptiveQM38ConditionalTransferDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
tactic='''  simp [AdaptiveQM40Context.residuals, AdaptiveQM38ResidualsDraft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add, map_mul] <;> ring
'''
proofs=[]
for j,(i,n) in enumerate(retained):
 proofs.append(f'''/-- Parent residual {i} and retained child residual {j}: {n}. -/
theorem residual{j:02d} (p : Fin 4 → ℤ) (v : Fin 38 → V) :
    (AdaptiveQM40Context.residuals p {i}).evalRing (fun k => ι (extend v k)) =
      (AdaptiveQM38ResidualsDraft.residuals p {j}).evalRing (fun k => ι (v k)) := by
'''+tactic+'\n')
for i in (20,24):
 proofs.append(f'''/-- Deleted parent residual {i} vanishes after the lift. -/
theorem dropped{i} (p : Fin 4 → ℤ) (v : Fin 38 → V) :
    (AdaptiveQM40Context.residuals p {i}).evalRing (fun k => ι (extend v k)) = 0 := by
'''+tactic+'\n')
end='''/-- The 29 matching residuals and the two vanished residuals yield the
whole graph identity over the difference ring, for arbitrary ports. -/
theorem evaluation_identity (p : Fin 4 → ℤ) (v : Fin 38 → V) :
    (AdaptiveQM40Context.literal p).evalRing (fun k => ι (extend v k)) =
      (AdaptiveQM38LiteralDraft.literal p).evalRing (fun k => ι (v k)) := by
  rw [← AdaptiveQM40Context.literal_eq, ← AdaptiveQM38ResidualsDraft.sum_eq_literal]
  simp only [AdaptiveQM40Context.sum, AdaptiveQM38ResidualsDraft.sum,
    Expr.evalRing_add, Expr.evalRing_mul]
'''
for j in range(29):end+=f'  have h{j:02d} := residual{j:02d} p v\n'
end+='  have hdrop20 := dropped20 p v\n  have hdrop24 := dropped24 p v\n'
end+='  simp only ['+', '.join(f'h{j:02d}' for j in range(29))+', hdrop20, hdrop24, zero_mul, add_zero]\n\n'
end+='''theorem evaluation_cut : AdaptiveQM38EvaluationCutDraft.EvaluationCut := by
  intro V _ _ v
  exact evaluation_identity CurrentWindowCarry2011.ports v

end DiophantineConsistency.AdaptiveQM38ResidualEvaluationDraft
#print axioms DiophantineConsistency.AdaptiveQM38ResidualEvaluationDraft.evaluation_identity
#print axioms DiophantineConsistency.AdaptiveQM38ResidualEvaluationDraft.evaluation_cut
'''
S=header+''.join(proofs)+end
(P/'AdaptiveQM38ResidualEvaluation.lean.src').write_text(S)
print(json.dumps({'scope':'generated inert source and syntactic child sum observation only; no Lean','retained_residuals':len(retained),'dropped_parent_indices':[20,24],'child_sum_exact_syntax':True,'child_residual_sha256':hashlib.sha256(R.encode()).hexdigest(),'evaluation_source_sha256':hashlib.sha256(S.encode()).hexdigest()},indent=2,sort_keys=True))
