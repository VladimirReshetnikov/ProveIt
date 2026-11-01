import DiophantineConsistency.IPRAReferenceInductionImage
import DiophantineConsistency.IPRASuccessorInduction

/-! Uncompiled draft: transfer of the reference induction axiom. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceInductionTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAReferenceRew IPRAReferenceInductionImage

def induction_image {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1))
    (h : IPRAQuantifierFree.OpenI φ) :
    IPRANativeTheory.nativeTheory ⊢! embed (IPRAEqualityOnlyReference.inductionAxiom φ) := by
  have heq : nativeSuccInduction (embed φ) =
      IPRASuccessorInduction.succInductionAxiom (embed φ) := rfl
  rw [embed_inductionAxiom, heq]
  exact IPRASuccessorInduction.successorInduction (embed φ) (embed_preserves_open φ h)

end DiophantineConsistency.IPRAReferenceInductionTransfer
