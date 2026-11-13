import DiophantineConsistency.IPRASelectedMatrixCharacteristic
import DiophantineConsistency.IPRAStandardSquareSums13
import DiophantineConsistency.IPRAStandardProduct13

/-! Compare the selected bounded refutation verifier with both no-zero
endpoints. The witness is a code for the bounded matrix, not an identified
external proof-checker code. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRASelectedCheckerConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRAStandardTheory
open IPRANativeFormula IPRANativeFormulaRew IPRATheoryHilbertBridge IPRACharacteristicTransfer
open IPRAFoundationZFCWitnessBound IPRAFoundationZFCMappedNegation FoundationHAConsistencyNormalization
open IPRASelectedMatrixCharacteristic IPRANativeDisjunctionWitness StrictSigmaOneInduction
open IPRABitConvention
open Rewriting

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

/-- The selected checker accepts a bound exactly when its PR Boolean code is 1. -/
def checkerRefutation (c : Code 1) : Sentenceᵢ language := ∃⁰ native (oneAtom c)

theorem selected_checker_endpoints : ∃ c : Code 1,
    Primrec (PRAFiniteFunctionCodes.eval c) ∧
    PRA ⊢ PRACharacteristicBit.bitSentence c ∧
    nativeTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c) ∧
    standardTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c) ∧
    standardTheory ⊢ (IPRAExpressionNative.nativeNoZero
      (AdaptiveEquationSyntax2011.positiveShift
        (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘
      ∼checkerRefutation c) ∧
    standardTheory ⊢ (IPRAExpressionNative.nativeNoZero
      AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼checkerRefutation c) := by
  obtain ⟨c,hprim,hbit,hcorrect⟩ := selected_matrix_characteristic
  let A : Semisentenceᵢ language 1 := native (oneAtom c)
  let B : Semisentenceᵢ language 1 := native (Semiformula.lMap embedding (bnd rho))
  have hAB : nativeTheory ⊢! ∀⁰ (A 🡒 B) := by
    have hc : nativeTheory ⊢! ∀⁰* (A 🡒 B) := by
      apply closeFamily 1 (A 🡒 B)
      intro e
      have h := Classical.choice (hcorrect e)
      simpa only [A,B,LogicalConnective.HomClass.map_imply,native_rew] using Entailment.K_left h
    simpa only [allClosure_succ,allClosure_zero] using hc
  have hBA : nativeTheory ⊢! ∀⁰ (B 🡒 A) := by
    have hc : nativeTheory ⊢! ∀⁰* (B 🡒 A) := by
      apply closeFamily 1 (B 🡒 A)
      intro e
      have h := Classical.choice (hcorrect e)
      simpa only [A,B,LogicalConnective.HomClass.map_imply,native_rew] using Entailment.K_right h
    simpa only [allClosure_succ,allClosure_zero] using hc
  have eAB : nativeTheory ⊢! (∃⁰ A) 🡒 ∃⁰ B := by
    have h := exImplyEx (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) (Rewriting.emb A) (Rewriting.emb B)
    have ht : nativeTheory ⊢! (∀⁰ (A 🡒 B)) 🡒 ((∃⁰ A) 🡒 ∃⁰ B) := by
      apply Theoryᵢ.ofHilbert
      simpa only [Rewriting.app_all,Rewriting.app_exs,Rew.q_emb,LogicalConnective.HomClass.map_imply] using h
    exact ht ⨀ hAB
  have eBA : nativeTheory ⊢! (∃⁰ B) 🡒 ∃⁰ A := by
    have h := exImplyEx (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) (Rewriting.emb B) (Rewriting.emb A)
    have ht : nativeTheory ⊢! (∀⁰ (B 🡒 A)) 🡒 ((∃⁰ B) 🡒 ∃⁰ A) := by
      apply Theoryᵢ.ofHilbert
      simpa only [Rewriting.app_all,Rewriting.app_exs,Rew.q_emb,LogicalConnective.HomClass.map_imply] using h
    exact ht ⨀ hBA
  have shape : native (Semiformula.lMap embedding boundedRefutation) = ∃⁰ B := by
    rfl
  have hneg : nativeTheory ⊢! ∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c := by
    have hbounded := Classical.choice selected_bounded_negation
    rw [shape] at hbounded
    have hequiv : nativeTheory ⊢! ∼(∃⁰ B) 🡘 ∼checkerRefutation c := by
      change nativeTheory ⊢! ∼(∃⁰ B) 🡘 ∼(∃⁰ A)
      exact Entailment.E_intro (Entailment.contra eAB) (Entailment.contra eBA)
    exact Entailment.E_trans hbounded hequiv
  have hstd : standardTheory ⊢ ∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c :=
    (provable_iff _).2 ⟨hneg⟩
  refine ⟨c,hprim,hbit,⟨hneg⟩,hstd,?_,?_⟩
  · exact ⟨Entailment.E_trans (Classical.choice IPRAStandardSquareSums13.literal_equivalence) (Classical.choice hstd)⟩
  · exact ⟨Entailment.E_trans (Classical.choice IPRAStandardProduct13.literal_equivalence) (Classical.choice hstd)⟩

#print axioms selected_checker_endpoints
end DiophantineConsistency.IPRASelectedCheckerConsistency
