module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeFormula
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
instance formulaCode_definable : 𝚺ᴬ₁-Function₂ (formulaCode : V→V→V) := formulaCode_defined.to_definable

theorem formulaCode_valid (param : V) {n p : V} (hp : IsSemiformula ℒₒᵣ n p) :
    IsSemiformula Presentation.language n (formulaCode param p) := by
  apply IsSemiformula.induction1 𝚺 (P:=fun n p => IsSemiformula Presentation.language n (formulaCode param p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k r ts hr ht
    rw [formulaCode_rel _ _ _ _ hr ht.isUTerm]
    exact atom_valid param hr ht
  · intro n k r ts hr ht
    rw [formulaCode_nrel _ _ _ _ hr ht.isUTerm]
    simpa using atom_valid param hr ht
  · intro n; rw [formulaCode_verum]; simp
  · intro n; rw [formulaCode_falsum]; simp
  · intro n p q hp hq ihp ihq
    rw [formulaCode_and _ _ _ hp.isUFormula hq.isUFormula]
    simpa using And.intro ihp ihq
  · intro n p q hp hq ihp ihq
    rw [formulaCode_or _ _ _ hp.isUFormula hq.isUFormula]
    simpa using And.intro ihp ihq
  · intro n p hp ih
    rw [formulaCode_all _ _ hp.isUFormula]
    simpa using ih
  · intro n p hp ih
    rw [formulaCode_exs _ _ hp.isUFormula]
    simpa using ih

#print axioms formulaCode_valid
end M6.PA.FoundationPAeqCode

