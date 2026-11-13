import DiophantineConsistency.IPRAFoundationZFCNegationTheory
import DiophantineConsistency.IPRANativeForwardTheory

/-! Exact ZFC normalization with its one remaining arithmetic premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCNegationOnePremise
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open IPRAFoundationZFCNegationTheory IPRANativeForwardTheory
variable {Λ : Hilbertᵢ ℒₒᵣ} {T : Theoryᵢ ℒₒᵣ Λ}

/-- Only the backward double-negation comparison remains as a T-premise. -/
def zfcConsistencyEquivalentOfBackward
    (hbackward : T ⊢! rhoᴺ 🡒 ∼∼nativeRefutation) :
    T ⊢! sourceSentenceᴺ 🡘 ∼nativeRefutation :=
  zfcConsistencyEquivalentNative (theoryNativeForward rho) hbackward
end DiophantineConsistency.IPRAFoundationZFCNegationOnePremise
