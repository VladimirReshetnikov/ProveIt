import DiophantineConsistency.IPRAFoundationZFCNegationOnePremise

/-! Map the exact ZFC sentence to any target language before GG translation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCMappedNegation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open IPRANativeFormula IPRANativeForwardTheory IPRARefutationNegationTheory
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- The native NNF reading after the actual source-language map. -/
noncomputable def mappedNativeRefutation (f : ℒₒᵣ →ᵥ L) : Sentenceᵢ L :=
  native (Semiformula.lMap f rho)

/-- Exact source mapped into an arbitrary theory language, with the sole
backward comparison kept as a theory proof premise. -/
def mappedZFCConsistencyEquivalent (f : ℒₒᵣ →ᵥ L)
    (hbackward : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 ∼∼mappedNativeRefutation f) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f := by
  rw [source_eq_neg_rho, LogicalConnective.HomClass.map_neg]
  exact theoryTranslatedNegationEquivalent (Semiformula.lMap f rho)
    (mappedNativeRefutation f) (theoryNativeForward (Semiformula.lMap f rho)) hbackward
end DiophantineConsistency.IPRAFoundationZFCMappedNegation
