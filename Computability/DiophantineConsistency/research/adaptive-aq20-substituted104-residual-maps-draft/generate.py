#!/usr/bin/env python3
"""Reconstruct inert AQ20 residual-map source; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent; D=P.parents[1]
old=(D/'Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean').read_bytes(); assert hashlib.sha256(old).hexdigest()=='68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d'
names=re.findall(r'^  !\[([^\n]+)\]$',old.decode(),re.M)[0].split(','); assert len(names)==13
idx=list(range(4))+list(range(6,13)); assert len(idx)==11
pre='''import AQ20Substituted104ConditionalTransfer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Proposed AQ20 residual identities and graph maps. No Lean check. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AQ20Substituted104ResidualMapsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AQ20Substituted104ConditionalTransferDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
simp='''  simp [AQ22Quotient110ResidualsDraft.residuals, AQ20Substituted104ResidualsDraft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    hb, map_add, map_mul, map_one] <;> ring
'''
for child,parent in enumerate(idx):
 pre+=f'''/-- Parent residual {parent} ({names[parent]}) after scale extension. -/
theorem relation{child:02d} (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hb : ((p 0 : ℤ) : DiffRing V)=ι beta) :
    (AQ22Quotient110ResidualsDraft.residuals p {parent}).evalRing (fun k => ι (extend beta v k)) =
      (AQ20Substituted104ResidualsDraft.residuals p {child}).evalRing (fun k => ι (v k)) := by
'''+simp+'\n'
for parent in (4,5):
 pre+=f'''/-- The removed parent scale-binding residual {parent} vanishes after extension. -/
theorem binding{parent:02d} (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hb : ((p 0 : ℤ) : DiffRing V)=ι beta) :
    (AQ22Quotient110ResidualsDraft.residuals p {parent}).evalRing (fun k => ι (extend beta v k)) = 0 := by
'''+simp+'\n'
pre+='''/-- Recover both model scale coordinates from the parent bindings.
The cast premise identifies the beta occurring in those bindings. -/
theorem parent_scales (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hb : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AQ22Quotient110LiteralDraft.literal p) v) :
    v 13=(1+v 0*beta)*((1+v 0*beta)*(1+v 0*beta))*(v 0*beta) ∧
    v 14=v 7*((1+v 0*beta)*(1+v 0*beta)) := by
  have hp := (AQ22Quotient110ResidualZerosDraft.all_residuals p v).mp hz
  have hs := (ModelDifferenceRing.internalZero_iff _ _).mp (hp 4)
  have ht := (ModelDifferenceRing.internalZero_iff _ _).mp (hp 5)
  constructor
  · apply ι_injective
    simp only [map_add,map_mul,map_one]
    simp [AQ22Quotient110ResidualsDraft.residuals, Expr.evalRing_add,
      Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
      Expr.evalRing_constant, Expr.evalRing_ofNat, hb] at hs
    linear_combination hs
  · apply ι_injective
    simp only [map_add,map_mul,map_one]
    simp [AQ22Quotient110ResidualsDraft.residuals, Expr.evalRing_add,
      Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
      Expr.evalRing_constant, Expr.evalRing_ofNat, hb] at ht
    linear_combination ht

/-- Once both parent bindings hold, projection and extension restore it. -/
theorem extend_project (beta : V) (v : Fin 22 → V)
    (hs : v 13=(1+v 0*beta)*((1+v 0*beta)*(1+v 0*beta))*(v 0*beta))
    (ht : v 14=v 7*((1+v 0*beta)*(1+v 0*beta))) :
    extend beta (project v)=v := by
  funext i
  fin_cases i <;> simp [extend, project, ←hs, ←ht]

/-- Extend a child zero using both binding identities and 11 common ones. -/
theorem extend_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hb : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AQ20Substituted104LiteralDraft.literal p) v) :
    InternalZero (AQ22Quotient110LiteralDraft.literal p) (extend beta v) := by
  have hc := (AQ20Substituted104ResidualZerosDraft.all_residuals p v).mp hz
  apply (AQ22Quotient110ResidualZerosDraft.all_residuals p (extend beta v)).mpr
  intro i
  fin_cases i
'''
for parent in range(13):
 pre+='  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr\n'
 if parent in (4,5): pre+=f'    exact binding{parent:02d} p beta v hb\n'
 else:
  child=idx.index(parent)
  pre+=f'''    rw [relation{child:02d} p beta v hb]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc {child})
'''
pre+='''
/-- Project any parent zero after recovering its scale bindings. -/
theorem project_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hb : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AQ22Quotient110LiteralDraft.literal p) v) :
    InternalZero (AQ20Substituted104LiteralDraft.literal p) (project v) := by
  have hp := (AQ22Quotient110ResidualZerosDraft.all_residuals p v).mp hz
  obtain ⟨hs,ht⟩ := parent_scales p beta v hb hz
  have hlift := extend_project beta v hs ht
  apply (AQ20Substituted104ResidualZerosDraft.all_residuals p (project v)).mpr
  intro i
  fin_cases i
'''
for child,parent in enumerate(idx):
 pre+=f'''  · have hparent : InternalZero (AQ22Quotient110ResidualsDraft.residuals p {parent})
        (extend beta (project v)) := by simpa only [hlift] using hp {parent}
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [relation{child:02d} p beta (project v) hb] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
pre+='''
/-- Proposed discharge of AQ20 graph obligations; AQ22 obligations remain
separate premises in the conditional endpoint. -/
theorem graphZeroObligations : GraphZeroObligations := by
  intro V _ _ beta _ hb
  constructor
  · intro v _ hz
    exact project_zero CurrentWindowCarry2011.ports beta v hb hz
  · intro v _ hz
    exact extend_zero CurrentWindowCarry2011.ports beta v hb hz

end DiophantineConsistency.AQ20Substituted104ResidualMapsDraft
#print axioms DiophantineConsistency.AQ20Substituted104ResidualMapsDraft.parent_scales
#print axioms DiophantineConsistency.AQ20Substituted104ResidualMapsDraft.extend_project
#print axioms DiophantineConsistency.AQ20Substituted104ResidualMapsDraft.extend_zero
#print axioms DiophantineConsistency.AQ20Substituted104ResidualMapsDraft.project_zero
#print axioms DiophantineConsistency.AQ20Substituted104ResidualMapsDraft.graphZeroObligations
'''
t=P/'AQ20Substituted104ResidualMaps.lean.src'
if '--initialize' in sys.argv: t.write_text(pre)
else: assert t.read_text()==pre
print(json.dumps({'scope':'inert source reconstruction, no Lean','source_sha256':hashlib.sha256(pre.encode()).hexdigest(),'parent_indices':idx,'equal_residuals':11,'vanishing_bindings':[4,5],'extension_cases':13,'projection_cases':11},sort_keys=True,indent=2))
