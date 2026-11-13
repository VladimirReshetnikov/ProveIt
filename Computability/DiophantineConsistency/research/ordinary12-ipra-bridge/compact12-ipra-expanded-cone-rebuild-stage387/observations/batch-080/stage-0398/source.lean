import DiophantineConsistency.IPRAWholeMatrixZFC
import DiophantineConsistency.PRAWitnessZFCRefutationBound
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAEquationComposition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open PRAWitnessZFCRefutationBound IPRAFoundationZFCMappedNegation
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def translatedSourceNegation : nativeTheory ⊢!
    (∼(Semiformula.lMap embedding refutation)ᴺ) 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ := by
  have h := Derivation.negDoubleNegation (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (Rewriting.emb (Semiformula.lMap embedding rho))
  have h' : nativeTheory ⊢! ∼(Semiformula.lMap embedding rho)ᴺ 🡘 (∼(Semiformula.lMap embedding rho))ᴺ := by
    apply Theoryᵢ.ofHilbert
    simpa only [Semiformula.emb_doubleNegation, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_iff] using h
  simpa only [source_eq_neg_rho, refutation, rho, LogicalConnective.HomClass.map_neg] using h'

def targetComparison
    (h : nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding) :
    nativeTheory ⊢! (∼(Semiformula.lMap embedding refutation)ᴺ) 🡘 ∼mappedNativeRefutation embedding :=
  Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left translatedSourceNegation) (Entailment.K_left h))
    (Entailment.C_trans (Entailment.K_right h) (Entailment.K_right translatedSourceNegation))

theorem equationComparison (φ : Sentenceᵢ language)
    (heq : nativeTheory ⊢ φ 🡘 ∼(Semiformula.lMap embedding refutation)ᴺ)
    (h : nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding) :
    nativeTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding := by
  obtain ⟨heq⟩ := heq
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left heq) (Entailment.K_left (targetComparison h)))
    (Entailment.C_trans (Entailment.K_right (targetComparison h)) (Entailment.K_right heq))⟩
end DiophantineConsistency.IPRAEquationComposition
