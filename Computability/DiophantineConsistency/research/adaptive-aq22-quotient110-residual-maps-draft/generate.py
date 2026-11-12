#!/usr/bin/env python3
"""Reconstruct/check inert residual-map source; no writes and no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent; D=P.parents[1]
def readpin(path,hash):
 b=(D/path).read_bytes(); assert hashlib.sha256(b).hexdigest()==hash,path; return b.decode()
old=readpin('Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean','68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d')
names=re.findall(r'^  !\[([^\n]+)\]$',old,re.M); assert len(names)==1
names=names[0].split(','); assert len(names)==13 and names[:2]==['A0','A1']
pre='''import AQ22Quotient110ConditionalTransfer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Source-only AQ22 quotient graph maps. This file has not been Lean checked. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AQ22Quotient110ResidualMapsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AQ22Quotient110ConditionalTransferDraft
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
simp='''  simp [AdaptiveAQ22Zeros.residuals, AQ22Quotient110ResidualsDraft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add, map_mul] <;> ring
'''
for i,n in enumerate(names):
 factor='' if i>=2 else f'ι (v {13+i}) * ι (v {13+i}) * '
 pre+=f'''/-- Parent residual {i} ({n}) after extension. -/
theorem relation{i:02d} (p : Fin 4 → ℤ) (v : Fin 22 → V) :
    (AdaptiveAQ22Zeros.residuals p {i}).evalRing (fun k => ι (extend v k)) =
      {factor}(AQ22Quotient110ResidualsDraft.residuals p {i}).evalRing (fun k => ι (v k)) := by
'''+simp+'\n'
pre+='''/-- Projection followed by extension restores both roots. -/
theorem extend_project (v : Fin 22 → V) (u t : V)
    (hu : v 18=v 13*u) (ht : v 19=v 14*t) :
    extend (project v u t)=v := by
  funext i
  fin_cases i <;> simp [extend, project, ←hu, ←ht]

/-- The two new norm residuals vanish from the quotient norm equations. -/
theorem project_norm0 (p : Fin 4 → ℤ) (v : Fin 22 → V) (u t : V)
    (hu : u*u=1+v 16*(v 16+(v 9+v 10))) :
    InternalZero (AQ22Quotient110ResidualsDraft.residuals p 0) (project v u t) := by
  rw [ModelDifferenceRing.internalZero_iff]
  have h := congrArg (ι : V →+* DiffRing V) hu
  simp only [map_add,map_mul,map_one] at h
  simp [AQ22Quotient110ResidualsDraft.residuals, project,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> linear_combination h

theorem project_norm1 (p : Fin 4 → ℤ) (v : Fin 22 → V) (u t : V)
    (ht : t*t=1+v 21*v 17) :
    InternalZero (AQ22Quotient110ResidualsDraft.residuals p 1) (project v u t) := by
  rw [ModelDifferenceRing.internalZero_iff]
  have h := congrArg (ι : V →+* DiffRing V) ht
  simp only [map_add,map_mul,map_one] at h
  simp [AQ22Quotient110ResidualsDraft.residuals, project,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> linear_combination h

/-- Every child zero extends to a parent zero; the scales need not be
positive in this direction. -/
theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (hz : InternalZero (AQ22Quotient110LiteralDraft.literal p) v) :
    InternalZero (AdaptiveAQ22Literal.literal p) (extend v) := by
  have hc := (AQ22Quotient110ResidualZerosDraft.all_residuals p v).mp hz
  apply (AdaptiveAQ22Zeros.sum_zero p (extend v)).mpr
  intro i
  fin_cases i
'''
for i in range(13):
 pre+='''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
'''
 if i<2:
  pre+=f'''    rw [relation{i:02d} p v, (ModelDifferenceRing.internalZero_iff _ _).mp (hc {i}), mul_zero]
'''
 else:
  pre+=f'''    rw [relation{i:02d} p v]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc {i})
'''
pre+='''
/-- A parent zero projects using the two exact quotient equations and
norm equations; existence and positivity are proved separately. -/
theorem project_zero (p : Fin 4 → ℤ) (v : Fin 22 → V) (u t : V)
    (hz : InternalZero (AdaptiveAQ22Literal.literal p) v)
    (hzu : v 18=v 13*u) (hdt : v 19=v 14*t)
    (hun : u*u=1+v 16*(v 16+(v 9+v 10))) (htn : t*t=1+v 21*v 17) :
    InternalZero (AQ22Quotient110LiteralDraft.literal p) (project v u t) := by
  have hp := (AdaptiveAQ22Zeros.sum_zero p v).mp hz
  have hlift := extend_project v u t hzu hdt
  apply (AQ22Quotient110ResidualZerosDraft.all_residuals p (project v u t)).mpr
  intro i
  fin_cases i
  · exact project_norm0 p v u t hun
  · exact project_norm1 p v u t htn
'''
for i in range(2,13):
 pre+=f'''  · have hparent : InternalZero (AdaptiveAQ22Zeros.residuals p {i})
        (extend (project v u t)) := by simpa only [hlift] using hp {i}
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [relation{i:02d} p (project v u t)] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
pre+='''
/-- Proposed discharge of both earlier graph obligations. This theorem,
like all source in the packet, remains unelaborated. -/
theorem graphZeroObligations : GraphZeroObligations := by
  intro V _ _
  constructor
  · intro v u t _ hz hzu hdt hun htn
    exact project_zero CurrentWindowCarry2011.ports v u t hz hzu hdt hun htn
  · intro v _ hz
    exact extend_zero CurrentWindowCarry2011.ports v hz

/-- Proposed closed client; quotient extraction and parent bridge are supplied
by the earlier source and its imported provider chain. -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift child) 🡘
      ∼mappedNativeRefutation embedding :=
  AQ22Quotient110ConditionalTransferDraft.native_equivalence graphZeroObligations

end DiophantineConsistency.AQ22Quotient110ResidualMapsDraft
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.relation00
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.relation01
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.project_norm0
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.project_norm1
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.extend_zero
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.project_zero
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.graphZeroObligations
#print axioms DiophantineConsistency.AQ22Quotient110ResidualMapsDraft.native_equivalence
'''
target=P/'AQ22Quotient110ResidualMaps.lean.src'
if '--initialize' in sys.argv: target.write_text(pre)
else: assert target.read_text()==pre
print(json.dumps({'scope':'inert source reconstruction; no Lean','source_sha256':hashlib.sha256(pre.encode()).hexdigest(),'residual_names':names,'factored_norm_identities':2,'equal_residual_identities':11,'project_cases':13,'extend_cases':13},sort_keys=True,indent=2))
