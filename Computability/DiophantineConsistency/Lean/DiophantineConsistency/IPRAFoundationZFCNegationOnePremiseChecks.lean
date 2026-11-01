import DiophantineConsistency.IPRAFoundationZFCNegationOnePremise

noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRAFoundationZFCNegationTheory
open DiophantineConsistency.IPRAFoundationZFCNegationOnePremise

example {Λ : Hilbertᵢ ℒₒᵣ} {T : Theoryᵢ ℒₒᵣ Λ}
    (hb : T ⊢! rhoᴺ 🡒 ∼∼nativeRefutation) :
    T ⊢! sourceSentenceᴺ 🡘 ∼nativeRefutation :=
  zfcConsistencyEquivalentOfBackward hb

#print axioms DiophantineConsistency.IPRAFoundationZFCNegationOnePremise.zfcConsistencyEquivalentOfBackward
