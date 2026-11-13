import DiophantineConsistency.IPRASelectedCheckerConsistency

set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASelectedCheckerNativeBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRAStandardTheory
open IPRANativeFormula IPRANativeFormulaRew IPRATheoryHilbertBridge IPRACharacteristicTransfer
open IPRAFoundationZFCMappedNegation IPRASelectedCheckerConsistency
open IPRANativeDisjunctionWitness IPRABitConvention
open Rewriting

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def nativeBitSentence (c : Code 1) : Sentenceᵢ language := ∀⁰* native (bitMatrix c)

theorem nativeBitOfClassical (c : Code 1) (hbit : PRA ⊢ PRACharacteristicBit.bitSentence c) :
    nativeTheory ⊢ nativeBitSentence c := by
  apply Nonempty.intro
  unfold nativeBitSentence
  apply closeFamily 1 (native (bitMatrix c))
  intro e
  rw [native_rew]
  exact transferOpen (bitMatrix c) (by simp [bitMatrix, Semiformula.Open])
    (by simpa only [PRACharacteristicBit.bitSentence, bitMatrix] using hbit) e

theorem selected_checker_boolean_endpoints : ∃ c : Code 1,
    Primrec (PRAFiniteFunctionCodes.eval c) ∧
    nativeTheory ⊢ nativeBitSentence c ∧
    standardTheory ⊢ nativeBitSentence c ∧
    standardTheory ⊢ (IPRAExpressionNative.nativeNoZero
      (AdaptiveEquationSyntax2011.positiveShift
        (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘
      ∼checkerRefutation c) ∧
    standardTheory ⊢ (IPRAExpressionNative.nativeNoZero
      AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼checkerRefutation c) := by
  obtain ⟨c, hp, hb, _, _, hs, ht⟩ := selected_checker_endpoints
  have hi := nativeBitOfClassical c hb
  exact ⟨c, hp, hi, (provable_iff _).2 hi, hs, ht⟩

#print axioms nativeBitOfClassical
#print axioms selected_checker_boolean_endpoints
end DiophantineConsistency.IPRASelectedCheckerNativeBit
