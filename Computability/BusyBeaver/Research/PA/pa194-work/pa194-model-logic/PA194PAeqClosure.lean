import PA194PAeqBindFormulaScope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def closeOne (p : V) : V := ^∀ (bindFormula 0 p)
noncomputable def closeIterBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “out seed. out = seed”
  succ := .mkSigma “out previous index seed. ∃ body, !bindFormulaGraph body 0 previous ∧ !qqAllDef out body”
noncomputable def closeIterConstruction : PR.Construction V closeIterBlueprint where
  zero p := p 0
  succ _ _ previous := closeOne previous
  zero_defined := .mk fun v => by simp [closeIterBlueprint]
  succ_defined := .mk fun v => by simp [closeIterBlueprint,closeOne]
noncomputable def close (n p : V) : V := closeIterConstruction.result ![p] n
noncomputable def closeGraph : 𝚺₁.Semisentence 3 := closeIterBlueprint.resultDef
instance close_defined : 𝚺₁-Function₂ (close : V → V → V) via closeGraph := .mk fun v => by
  have h := (closeIterConstruction (V := V)).result_defined.defined v
  simpa [closeGraph,close,Matrix.comp_vecCons',Matrix.constant_eq_singleton] using h
@[simp] theorem close_zero (p : V) : close 0 p = p := by simp [close,closeIterConstruction]
@[simp] theorem close_succ (n p : V) : close (n+1) p = closeOne (close n p) := by simp [close,closeIterConstruction]
theorem closeOne_scope {n p : V} (hp : IsSemiformula PA194PAeq.language n p) :
    IsSemiformula PA194PAeq.language n (closeOne p) := by
  apply IsSemiformula.all.mpr
  exact bindFormula_scope hp.isUFormula 0 n (by simp) hp
theorem close_scope (n : V) {arity p : V} (hp : IsSemiformula PA194PAeq.language arity p) :
    IsSemiformula PA194PAeq.language arity (close n p) := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simpa using hp
  | succ n ih => simpa using closeOne_scope ih
#print axioms close_defined
#print axioms close_zero
#print axioms close_succ
#print axioms close_scope
end generic
end PA194PAeqBind
