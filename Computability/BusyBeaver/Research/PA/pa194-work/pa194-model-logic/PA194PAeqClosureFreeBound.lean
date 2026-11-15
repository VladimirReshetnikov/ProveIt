import PA194PAeqFreeBoundFormulaBind
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem closeOne_freeBound {p : V} (hp : IsUFormula PA194PAeq.language p) :
    formulaFreeBound (closeOne p) = formulaFreeBound p - 1 := by
  rw [closeOne,formulaFreeBound_all (bindFormula_uformula hp),formulaFreeBound_bind hp 0]
theorem close_freeBound (n : V) {arity p : V} (hp : IsSemiformula PA194PAeq.language arity p) :
    formulaFreeBound (close n p) = formulaFreeBound p - n := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ n ih =>
    rw [close_succ,closeOne_freeBound (close_scope n hp).isUFormula,ih]
    simp [Arithmetic.sub_sub]
#print axioms closeOne_freeBound
#print axioms close_freeBound
end generic
end PA194PAeqBind
