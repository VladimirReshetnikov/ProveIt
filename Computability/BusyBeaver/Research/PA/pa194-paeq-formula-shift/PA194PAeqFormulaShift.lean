import PA194PAeqFormulaSubst
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_isUFormula (param : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsUFormula PA194PAeq.language (formulaCode param p) := (formulaCode_valid param hp.isSemiformula).isUFormula

theorem formulaCode_shift (param : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (Bootstrapping.shift ℒₒᵣ p)=Bootstrapping.shift PA194PAeq.language (formulaCode param p) := by
  apply IsUFormula.induction1 𝚺 (P:=fun p => formulaCode param (Bootstrapping.shift ℒₒᵣ p)=Bootstrapping.shift PA194PAeq.language (formulaCode param p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r ts hr ht
    rw [shift_rel hr ht,formulaCode_rel _ _ _ _ hr ht.termShiftVec,formulaCode_rel _ _ _ _ hr ht]
    exact atomCode_shift param hr ht
  · intro k r ts hr ht
    rw [shift_nrel hr ht,formulaCode_nrel _ _ _ _ hr ht.termShiftVec,formulaCode_nrel _ _ _ _ hr ht,
      atomCode_shift param hr ht,shift_neg (atom_valid param hr ht.isSemitermVec)]
  · rw [shift_verum,formulaCode_verum,shift_verum]
  · rw [shift_falsum,formulaCode_falsum,shift_falsum]
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq,formulaCode_and _ _ _ hp.shift hq.shift,formulaCode_and _ _ _ hp hq,
      shift_and (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),ihp,ihq]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq,formulaCode_or _ _ _ hp.shift hq.shift,formulaCode_or _ _ _ hp hq,
      shift_or (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),ihp,ihq]
  · intro p hp ih
    rw [shift_all hp,formulaCode_all _ _ hp.shift,formulaCode_all _ _ hp,
      shift_all (formulaCode_isUFormula param hp),ih]
  · intro p hp ih
    rw [shift_exs hp,formulaCode_exs _ _ hp.shift,formulaCode_exs _ _ hp,
      shift_exs (formulaCode_isUFormula param hp),ih]

#print axioms formulaCode_shift
end PA194PAeqTermBlueprint
