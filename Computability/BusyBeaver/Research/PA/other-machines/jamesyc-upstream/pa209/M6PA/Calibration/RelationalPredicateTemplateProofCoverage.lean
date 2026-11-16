module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateProofBounds
public import M6PA.Calibration.RelationalPredicateTemplateTargetShift
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Finite occurrence coverage through every node of the given host proof.
The universal premise uses its actual fresh target free-variable environment. -/
def ProofCovered : {Γ : LK.Sequent sourceLanguage} → LK.Derivation Γ → V → Prop
  | Γ,d,f => SequentCovered Γ f ∧ match d with
    | .identity _ _ => True
    | .cut dp dn => ProofCovered dp f ∧ ProofCovered dn f
    | .contraction dp => ProofCovered dp f
    | .weakening dp => ProofCovered dp f
    | .verum => True
    | .or dp => ProofCovered dp f
    | .and dp dq => ProofCovered dp f ∧ ProofCovered dq f
    | .all dp => ProofCovered dp (qqFvar 0∷targetShiftTerms f)
    | @LK.Derivation.exs _ _ _ t dp =>
        (∀i,t.FVar? i→(i:V)<len f) ∧ ProofCovered dp f

theorem ProofCovered.sequent {Γ : LK.Sequent sourceLanguage} {d : LK.Derivation Γ} {f : V}
    (h : ProofCovered d f) : SequentCovered Γ f := by
  unfold ProofCovered at h
  exact h.1
#print axioms ProofCovered.sequent
end M6.PA.RelationalPredicateTemplate

