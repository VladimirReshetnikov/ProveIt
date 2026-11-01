import DiophantineConsistency.IPRARefutationNegationTheory
import DiophantineConsistency.IPRANativeForwardTheory

/-! A conditional intuitionistic bridge from a bounded witness sentence. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRARefutationWitnessBridge
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open IPRANativeFormula IPRANativeForwardTheory IPRARefutationNegationTheory
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- A translated witness bound, double-negated native witness comparison,
and native witness erasure imply the required backward comparison. -/
def backwardOfWitness (ρ bound : Sentence L)
    (hbound : T ⊢! ρᴺ 🡒 boundᴺ)
    (hcompare : T ⊢! boundᴺ 🡒 ∼∼native bound)
    (herase : T ⊢! native bound 🡒 native ρ) :
    T ⊢! ρᴺ 🡒 ∼∼native ρ :=
  Entailment.C_trans hbound
    (Entailment.C_trans hcompare (Entailment.contra (Entailment.contra herase)))

/-- Conditional full negation comparison. None of its three premises is
asserted here and no double-negated existential witness is extracted. -/
def negationOfWitness (ρ bound : Sentence L)
    (hbound : T ⊢! ρᴺ 🡒 boundᴺ)
    (hcompare : T ⊢! boundᴺ 🡒 ∼∼native bound)
    (herase : T ⊢! native bound 🡒 native ρ) :
    T ⊢! (∼ρ)ᴺ 🡘 ∼native ρ :=
  theoryTranslatedNegationEquivalent ρ (native ρ) (theoryNativeForward ρ)
    (backwardOfWitness ρ bound hbound hcompare herase)
end DiophantineConsistency.IPRARefutationWitnessBridge
