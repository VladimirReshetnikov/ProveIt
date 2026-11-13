module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLK
public import M6PA.Calibration.RelationalPredicateTemplateProofCoverageBound
@[expose] public section
/-! Finite host LK soundness with one explicit numerical environment bound. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
theorem template_lk_sound_of_bound {Γ : LK.Sequent sourceLanguage}
    (d : LK.Derivation Γ) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound d : V) ≤ len f) :
    Derivable T (sequentValue Γ P f) :=
  template_lk_sound d hP hf (proofCovered_of_bound d hf hb)
#print axioms template_lk_sound_of_bound
end M6.PA.RelationalPredicateTemplate

