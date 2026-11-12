#!/usr/bin/env python3
"""Generate/check 8 source-only model residual identities; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
s='''import AQ17Forced105ConditionalTransfer
import DiophantineConsistency.ModelDifferenceRing
import Mathlib.Tactic.Ring

/-! Source-only mixed-shift residual comparison; no Lean. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AQ17Forced105EvaluationDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AQ17Forced105ConditionalTransferDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
for i in range(8):
 s+=f'''theorem relation{i:02d} (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    (AQ17Forced105ResidualsDraft.residuals p {i}).evalRing (fun k => ι (v k)) =
      (AQ17Factored94ResidualsDraft.residuals p {i}).evalRing (fun k => ι (mixed v k)) := by
  simp [AQ17Forced105ResidualsDraft.residuals, AQ17Factored94ResidualsDraft.residuals,
    mixed, Forced, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> ring

'''
s+='''/-- Equality of the complete evaluated sums, using all eight identities. -/
theorem evaluation (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    (child p).evalRing (fun k => ι (v k)) =
      (parent p).evalRing (fun k => ι (mixed v k)) := by
  change (AQ17Forced105LiteralDraft.literal p).evalRing (fun k => ι (v k)) =
    (AQ17Factored94LiteralDraft.literal p).evalRing (fun k => ι (mixed v k))
  rw [←AQ17Forced105ResidualsDraft.sum_eq_literal, ←AQ17Factored94ResidualsDraft.sum_eq_literal]
  simp only [AQ17Forced105ResidualsDraft.sum, AQ17Factored94ResidualsDraft.sum,
    Expr.evalRing_add, Expr.evalRing_mul, relation00 p v, relation01 p v,
    relation02 p v, relation03 p v, relation04 p v, relation05 p v,
    relation06 p v, relation07 p v]

theorem zeroEquivalence : ZeroEquivalence := by
  intro V _ _ p v
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff, evaluation p v]
end DiophantineConsistency.AQ17Forced105EvaluationDraft
#print axioms DiophantineConsistency.AQ17Forced105EvaluationDraft.evaluation
#print axioms DiophantineConsistency.AQ17Forced105EvaluationDraft.zeroEquivalence
'''
t=P/'AQ17Forced105Evaluation.lean.src'
if '--initialize' in sys.argv:t.write_text(s)
else:assert t.read_text()==s
print(json.dumps({'scope':'inert evaluation source; no Lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'residual_identities':8},sort_keys=True,indent=2))
