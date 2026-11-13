import DiophantineConsistency.IPRARefutationNegationTheory
import DiophantineConsistency.IPRANativeFormula
import DiophantineConsistency.FoundationHAConsistencyNormalization

/-! Conditional theory-level normalization of Foundation's exact ZFC source. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCNegationTheory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open IPRARefutationNegationTheory

variable {Λ : Hilbertᵢ ℒₒᵣ} {T : Theoryᵢ ℒₒᵣ Λ}

/-- The exact Foundation ZFC consistency sentence's GG image is the native
negated predicate, assuming the two displayed comparison proofs in T. -/
def zfcConsistencyEquivalent (ordinaryRefutation : Sentenceᵢ ℒₒᵣ)
    (hforward : T ⊢! ordinaryRefutation 🡒 rhoᴺ)
    (hbackward : T ⊢! rhoᴺ 🡒 ∼∼ordinaryRefutation) :
    T ⊢! sourceSentenceᴺ 🡘 ∼ordinaryRefutation := by
  rw [source_eq_neg_rho]
  exact theoryTranslatedNegationEquivalent rho ordinaryRefutation hforward hbackward
/-- The ordinary intuitionistic NNF reading of the literal ZFC refutation. -/
noncomputable def nativeRefutation : Sentenceᵢ ℒₒᵣ := IPRANativeFormula.native rho

/-- Exact native ZFC instance, still conditional on both T-proofs. -/
def zfcConsistencyEquivalentNative
    (hforward : T ⊢! nativeRefutation 🡒 rhoᴺ)
    (hbackward : T ⊢! rhoᴺ 🡒 ∼∼nativeRefutation) :
    T ⊢! sourceSentenceᴺ 🡘 ∼nativeRefutation :=
  zfcConsistencyEquivalent nativeRefutation hforward hbackward
end DiophantineConsistency.IPRAFoundationZFCNegationTheory
