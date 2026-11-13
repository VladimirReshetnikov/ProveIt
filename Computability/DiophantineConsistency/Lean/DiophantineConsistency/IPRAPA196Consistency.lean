import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRANativeForwardTheory
import DiophantineConsistency.IPRARefutationNegationTheory
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! # Binding Foundation PA consistency in the iPRA language

`paConsistency` is Foundation's actual arithmetized consistency sentence
for its classical PA theory, and `paRefutation` is the positive provability
predicate occurring underneath it.  The ordinary intuitionistic sentence
`nativePAConsistency` negates the native reading of the mapped refutation
formula. `translatedPAConsistency` is instead the Gödel–Gentzen image of the
mapped classical consistency sentence; their comparison below is conditional
on a backward double-negation proof.

The standard-natural-number theorem checks the source coding only.  In
particular, this file neither identifies Foundation's PA proof coding with the
separately imported PA196 project's FFL coding nor defines a Turing-machine
halting sentence. It proves no iPRA consistency/halting equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAPA196Consistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeFormula IPRAStandardTheory IPRANativeForwardTheory IPRARefutationNegationTheory

/-- Foundation's actual arithmetic consistency sentence for its classical PA. -/
def paConsistency : ArithmeticSentence := ((𝗣𝗔 : ArithmeticTheory).consistent : ArithmeticSentence)
/-- The positive arithmetized PA-refutation predicate used by that sentence. -/
def paRefutation : ArithmeticSentence := provabilityPred (𝗣𝗔 : ArithmeticTheory) (⊥ : ArithmeticSentence)
theorem paConsistency_eq : paConsistency = ∼paRefutation := rfl

theorem paRefutation_sigma_one : Hierarchy 𝚺 1 paRefutation := by
  simpa only [paRefutation, provabilityPred'_val] using
    (provabilityPred' (𝗣𝗔 : ArithmeticTheory) (⊥ : ArithmeticSentence)).sigma_prop

/-- Map the classical PA-refutation syntax into the PR-code language. -/
def mappedPARefutation : Sentence language := Semiformula.lMap embedding paRefutation
/-- Read that NNF syntax using intuitionistic logical connectives. -/
def nativePARefutation : Sentenceᵢ language := native mappedPARefutation
/-- The ordinary negative form: no refutation in the chosen PA coding. -/
def nativePAConsistency : Sentenceᵢ language := ∼nativePARefutation
/-- GG translation of Foundation's actual mapped PA consistency sentence. -/
def translatedPAConsistency : Sentenceᵢ language := (Semiformula.lMap embedding paConsistency)ᴺ

/-- This only identifies the standard-model interpretation of the source. -/
theorem paConsistency_standard : paConsistency.Evalb (M := ℕ) ![] ↔ Entailment.Consistent (𝗣𝗔 : ArithmeticTheory) := by
  simpa only [paConsistency, consistent.defined] using (standard_consistent (𝗣𝗔 : ArithmeticTheory))

/-- Standard iPRA proves the forward comparison with the GG image. -/
def native_refutation_to_gg : standardTheory ⊢! nativePARefutation 🡒 mappedPARefutationᴺ :=
  theoryNativeForward mappedPARefutation

/-- Conditional comparison; supplying this backward proof remains a task. -/
def consistency_comparison
    (hbackward : standardTheory ⊢! mappedPARefutationᴺ 🡒 ∼∼nativePARefutation) :
    standardTheory ⊢! translatedPAConsistency 🡘 nativePAConsistency := by
  unfold translatedPAConsistency nativePAConsistency nativePARefutation
  rw [paConsistency_eq, LogicalConnective.HomClass.map_neg]
  exact theoryTranslatedNegationEquivalent mappedPARefutation (native mappedPARefutation)
    (theoryNativeForward mappedPARefutation) hbackward
end DiophantineConsistency.IPRAPA196Consistency
