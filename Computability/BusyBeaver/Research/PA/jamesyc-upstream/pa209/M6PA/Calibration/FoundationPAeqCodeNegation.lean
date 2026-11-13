module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeFormulaCalibration
@[expose] public section

/-! Exact NNF negation compatibility in arbitrary IΣ₁ models. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_isUFormula (param : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsUFormula Presentation.language (formulaCode param p) :=
  (formulaCode_valid param hp.isSemiformula).isUFormula

theorem formulaCode_neg (param : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (neg ℒₒᵣ p)=neg Presentation.language (formulaCode param p) := by
  apply IsUFormula.induction1 𝚺 (P:=fun p => formulaCode param (neg ℒₒᵣ p)=neg Presentation.language (formulaCode param p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r ts hr ht
    rw [neg_rel hr ht,formulaCode_nrel _ _ _ _ hr ht,formulaCode_rel _ _ _ _ hr ht]
  · intro k r ts hr ht
    rw [neg_nrel hr ht,formulaCode_rel _ _ _ _ hr ht,formulaCode_nrel _ _ _ _ hr ht]
    exact (atom_valid param hr ht.isSemitermVec).isUFormula.neg_neg.symm
  · rw [neg_verum,formulaCode_falsum,formulaCode_verum,neg_verum]
  · rw [neg_falsum,formulaCode_verum,formulaCode_falsum,neg_falsum]
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq,formulaCode_or _ _ _ hp.neg hq.neg,formulaCode_and _ _ _ hp hq,
      neg_and (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),ihp,ihq]
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq,formulaCode_and _ _ _ hp.neg hq.neg,formulaCode_or _ _ _ hp hq,
      neg_or (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),ihp,ihq]
  · intro p hp ih
    rw [neg_all hp,formulaCode_exs _ _ hp.neg,formulaCode_all _ _ hp,
      neg_all (formulaCode_isUFormula param hp),ih]
  · intro p hp ih
    rw [neg_ex hp,formulaCode_all _ _ hp.neg,formulaCode_exs _ _ hp,
      neg_ex (formulaCode_isUFormula param hp),ih]

#print axioms formulaCode_isUFormula
#print axioms formulaCode_neg
end M6.PA.FoundationPAeqCode

