#!/usr/bin/env python3
"""Reconstruct inert AQ17 residual-map source; never run Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
source=(D/'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Residuals.lean.src').read_bytes()
assert hashlib.sha256(source).hexdigest()=='15d6509b3bc49521b1b1e11b7090c9a30d43643116d471e6b596a4f5304acf4d'
names=re.findall(r'^  !\[([^\n]+)\]$',source.decode(),re.M)[0].split(',');assert len(names)==11
idx=[0,1,2,3,4,7,8,9];dropped=[5,6,10];assert sorted(idx+dropped)==list(range(11))
pre='''import AQ17Factored94ConditionalTransfer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Proposed AQ17/94 residual comparisons and graph maps; no Lean check. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AQ17Factored94ResidualMapsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AQ17Factored94ConditionalTransferDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
simp='''  simp [AQ20Substituted104ResidualsDraft.residuals, AQ17Factored94ResidualsDraft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add,map_mul] <;> ring
'''
for child,parent in enumerate(idx):
 pre+=f'''/-- Parent residual {parent} ({names[parent]}) after extension. -/
theorem relation{child:02d} (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    (AQ20Substituted104ResidualsDraft.residuals p {parent}).evalRing (fun k => ι (extend v k)) =
      (AQ17Factored94ResidualsDraft.residuals p {child}).evalRing (fun k => ι (v k)) := by
'''+simp+'\n'
for parent in dropped:
 pre+=f'''/-- Parent binding residual {parent} ({names[parent]}) vanishes after extension. -/
theorem binding{parent:02d} (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    (AQ20Substituted104ResidualsDraft.residuals p {parent}).evalRing (fun k => ι (extend v k)) = 0 := by
'''+simp+'\n'
pre+='''/-- Recover the three parent bindings by injectivity of the model embedding. -/
theorem parent_bindings (p : Fin 4 → ℤ) (v : Fin 20 → V)
    (hz : InternalZero (AQ20Substituted104LiteralDraft.literal p) v) :
    v 14=(v 6*v 7)*(v 7*(v 9+v 10)) ∧
    v 15=(v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10)) ∧
    v 19=3+4*(v 6*v 7+v 7)+(v 6*v 7+v 7)*(v 6*v 7+v 7) := by
  have hp := (AQ20Substituted104ResidualZerosDraft.all_residuals p v).mp hz
  have he := (ModelDifferenceRing.internalZero_iff _ _).mp (hp 5)
  have hc := (ModelDifferenceRing.internalZero_iff _ _).mp (hp 6)
  have hd := (ModelDifferenceRing.internalZero_iff _ _).mp (hp 10)
  constructor
  · apply ι_injective
    simp only [map_add,map_mul]
    simp [AQ20Substituted104ResidualsDraft.residuals, Expr.evalRing_add,
      Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
      Expr.evalRing_constant, Expr.evalRing_ofNat] at he
    linear_combination he
  constructor
  · apply ι_injective
    simp only [map_add,map_mul]
    simp [AQ20Substituted104ResidualsDraft.residuals, Expr.evalRing_add,
      Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
      Expr.evalRing_constant, Expr.evalRing_ofNat] at hc
    linear_combination hc
  · apply ι_injective
    simp only [map_add,map_mul,map_ofNat]
    simp [AQ20Substituted104ResidualsDraft.residuals, Expr.evalRing_add,
      Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
      Expr.evalRing_constant, Expr.evalRing_ofNat] at hd
    linear_combination hd

theorem extend_project (v : Fin 20 → V)
    (he : v 14=(v 6*v 7)*(v 7*(v 9+v 10)))
    (hc : v 15=(v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10)))
    (hd : v 19=3+4*(v 6*v 7+v 7)+(v 6*v 7+v 7)*(v 6*v 7+v 7)) :
    extend (project v)=v := by
  funext i
  fin_cases i <;> simp [extend, project, ←he, ←hc, ←hd]

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (AQ17Factored94LiteralDraft.literal p) v) :
    InternalZero (AQ20Substituted104LiteralDraft.literal p) (extend v) := by
  have hc := (AQ17Factored94ResidualZerosDraft.all_residuals p v).mp hz
  apply (AQ20Substituted104ResidualZerosDraft.all_residuals p (extend v)).mpr
  intro i
  fin_cases i
'''
for parent in range(11):
 pre+='  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr\n'
 if parent in dropped:pre+=f'    exact binding{parent:02d} p v\n'
 else:
  child=idx.index(parent)
  pre+=f'''    rw [relation{child:02d} p v]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc {child})
'''
pre+='''
theorem project_zero (p : Fin 4 → ℤ) (v : Fin 20 → V)
    (hz : InternalZero (AQ20Substituted104LiteralDraft.literal p) v) :
    InternalZero (AQ17Factored94LiteralDraft.literal p) (project v) := by
  have hp := (AQ20Substituted104ResidualZerosDraft.all_residuals p v).mp hz
  obtain ⟨he,hc,hd⟩ := parent_bindings p v hz
  have hlift := extend_project v he hc hd
  apply (AQ17Factored94ResidualZerosDraft.all_residuals p (project v)).mpr
  intro i
  fin_cases i
'''
for child,parent in enumerate(idx):
 pre+=f'''  · have hparent : InternalZero (AQ20Substituted104ResidualsDraft.residuals p {parent})
        (extend (project v)) := by simpa only [hlift] using hp {parent}
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [relation{child:02d} p (project v)] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
pre+='''
theorem graphZeroObligations : GraphZeroObligations := by
  intro V _ _
  constructor
  · intro v _ hz
    exact project_zero CurrentWindowCarry2011.ports v hz
  · intro v _ hz
    exact extend_zero CurrentWindowCarry2011.ports v hz

end DiophantineConsistency.AQ17Factored94ResidualMapsDraft
#print axioms DiophantineConsistency.AQ17Factored94ResidualMapsDraft.parent_bindings
#print axioms DiophantineConsistency.AQ17Factored94ResidualMapsDraft.extend_project
#print axioms DiophantineConsistency.AQ17Factored94ResidualMapsDraft.extend_zero
#print axioms DiophantineConsistency.AQ17Factored94ResidualMapsDraft.project_zero
#print axioms DiophantineConsistency.AQ17Factored94ResidualMapsDraft.graphZeroObligations
'''
t=P/'AQ17Factored94ResidualMaps.lean.src'
if '--initialize' in sys.argv:t.write_text(pre)
else:assert t.read_text()==pre
print(json.dumps({'scope':'inert source reconstruction; no Lean','source_sha256':hashlib.sha256(pre.encode()).hexdigest(),'parent_indices':idx,'equal_residuals':8,'vanishing_bindings':dropped,'extension_cases':11,'projection_cases':8},sort_keys=True,indent=2))
