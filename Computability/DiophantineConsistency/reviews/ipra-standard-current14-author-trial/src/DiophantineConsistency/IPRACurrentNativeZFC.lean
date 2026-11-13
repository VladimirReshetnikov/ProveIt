import DiophantineConsistency.IPRABoundedRhoZFC
import DiophantineConsistency.IPRAEquationComposition
import DiophantineConsistency.IPRACurrentTranslatedRefutation

/-! The literal displayed 14-variable equation versus native ZFC refutation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRACurrentNativeZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRANoZeroUnary DiophantineConsistency.FoundationHANoZero
open DiophantineConsistency.ObjectCurrentEquation2011
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAFoundationZFCMappedNegation

def noZero14 : Sentenceᵢ language := ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
  ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1)),
    Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))]))

theorem equivalence14 : nativeTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding :=
  DiophantineConsistency.IPRAEquationComposition.equationComparison noZero14
    DiophantineConsistency.IPRACurrentTranslatedRefutation.current_translated_refutation
    DiophantineConsistency.IPRABoundedRhoZFC.zfcEquiv
end DiophantineConsistency.IPRACurrentNativeZFC
