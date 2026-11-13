import DiophantineConsistency.IPRAErasedRemainingObligations
import DiophantineConsistency.IPRAReferencePredecessor

/-! Exploratory native-to-reference transport conditional on the single
remaining induction image. Coherent source replay and that image are open. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAErasedInductionObligation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAEqualityOnlyReference

theorem transfer
    (hi : ∀ {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)),
      IPRAQuantifierFree.OpenI φ → referenceTheory ⊢ erase (IPRANativeInduction.inductionAxiom φ))
    {σ : Sentenceᵢ PRALanguage.language} (h : IPRANativeTheory.nativeTheory ⊢ σ) :
    referenceTheory ⊢ erase σ :=
  IPRAErasedRemainingObligations.transfer ⟨IPRAReferencePredecessor.successorInjectivityImage⟩ hi h

end DiophantineConsistency.IPRAErasedInductionObligation
