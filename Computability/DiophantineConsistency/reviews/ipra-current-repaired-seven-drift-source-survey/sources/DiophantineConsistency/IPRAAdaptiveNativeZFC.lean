import DiophantineConsistency.IPRABoundedRhoZFC
import DiophantineConsistency.IPRAEquationComposition
import DiophantineConsistency.IPRA86TranslatedRefutation
import DiophantineConsistency.IPRA87TranslatedRefutation

/-! The displayed 86- and 87-operation equations against native ZFC
refutation, conditional only on the checked candidate native theory axioms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAdaptiveNativeZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRANoZeroUnary DiophantineConsistency.FoundationHANoZero
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAFoundationZFCMappedNegation

def noZero86 : Sentenceᵢ language := ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
  ![Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.1)),
    Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.2))]))

def noZero87 : Sentenceᵢ language := ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
  ![Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1)),
    Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2))]))

theorem equivalence86 : nativeTheory ⊢ noZero86 🡘 ∼mappedNativeRefutation embedding :=
  DiophantineConsistency.IPRAEquationComposition.equationComparison noZero86
    DiophantineConsistency.IPRA86TranslatedRefutation.translated_refutation
    DiophantineConsistency.IPRABoundedRhoZFC.zfcEquiv

theorem equivalence87 : nativeTheory ⊢ noZero87 🡘 ∼mappedNativeRefutation embedding :=
  DiophantineConsistency.IPRAEquationComposition.equationComparison noZero87
    DiophantineConsistency.IPRA87TranslatedRefutation.translated_refutation
    DiophantineConsistency.IPRABoundedRhoZFC.zfcEquiv
end DiophantineConsistency.IPRAAdaptiveNativeZFC
