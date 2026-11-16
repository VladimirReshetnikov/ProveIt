module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionCalibration
@[expose] public section

/-! Literal all-model source induction-body decoding. Only the two fixed
quoted term vectors are normalized; the arbitrary source formula is untouched. -/
namespace M6.PA.NumericPAeqInductionSourceBody
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FoundationPAeqCode
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language

theorem zero_substitution_vector :
    (paeqSubstCode (Presentation.zero : SyntacticTerm L) : V)=(qqFunc 0 0 0)∷0 := by
  rw [paeqSubstCode_cast]
  rw [Presentation.quote_zero]

theorem successor_substitution_vector :
    (paeqSubstCode (Presentation.succ (.bvar 0) : SyntacticSemiterm L 1) : V)=
      (qqFunc 1 1 (qqBvar 0∷0))∷0 := by
  rw [paeqSubstCode_cast]
  rw [Presentation.quote_successor]
  simp

theorem targetIndBody_eq (p:V) :
    targetIndBody p = imp L (subst L (qqFunc 0 0 0∷0) p)
      (imp L (qqAll (imp L p (subst L (qqFunc 1 1 (qqBvar 0∷0)∷0) p))) (qqAll p)) := by
  simp only [targetIndBody,zero_substitution_vector,successor_substitution_vector]
#print axioms zero_substitution_vector
#print axioms successor_substitution_vector
#print axioms targetIndBody_eq
end M6.PA.NumericPAeqInductionSourceBody

