import DiophantineConsistency.PRAExpressionZFCStrict
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAEquationComposition
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Generic expression endpoint, conditional on an explicit bridge or classical comparison. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAExpressionNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound
open IPRANativeTheory IPRAFoundationZFCMappedNegation

def nativeNoZero {n : ℕ} (e : Expr (Fin n)) : Sentenceᵢ language := ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
  ![Semiterm.lMap embedding (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1)),
    Semiterm.lMap embedding (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

theorem comparison_of_pra {n : ℕ} (e : Expr (Fin n))
    (hc : PRA ⊢ (Semiformula.lMap embedding (classicalNoZero e)) 🡘
      ∼(Semiformula.lMap embedding refutation)) :
    nativeTheory ⊢ nativeNoZero e 🡘 ∼mappedNativeRefutation embedding := by
  have ht := IPRAConditionalComparison.translated_comparison IPRAFullGGTransfer.axiom_images
    (Semiformula.lMap embedding (classicalNoZero e)) (Semiformula.lMap embedding refutation) hc
  have hn : (Semiformula.lMap embedding (classicalNoZero e))ᴺ = nativeNoZero e := by
    simpa only [classicalNoZero, nativeNoZero, PRANoZeroUnary.noZero] using
      IPRAMappedNoZero.mapped_gg_noZero n
        (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1))
        (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2))
  have heq : nativeTheory ⊢ nativeNoZero e 🡘 ∼(Semiformula.lMap embedding refutation)ᴺ := by
    simpa only [hn] using ht
  exact IPRAEquationComposition.equationComparison (nativeNoZero e) heq IPRABoundedRhoZFC.zfcEquiv

theorem equivalence_of_isigma1 {n : ℕ} (e : Expr (Fin n))
    (h : 𝗜𝚺₁ ⊢ (classicalNoZero e 🡘 FoundationZFCConsistencyNat.sourceSentence)) :
    nativeTheory ⊢ nativeNoZero e 🡘 ∼mappedNativeRefutation embedding :=
  comparison_of_pra e (by
    simpa only [LogicalConnective.HomClass.map_neg] using
      PRAExpressionZFCStrict.comparison_of_isigma1 e h)

theorem equivalence_of_bridge {n : ℕ} (e : Expr (Fin n)) (hp : HAExpressionAssembly.PolynomialBridge e) :
    nativeTheory ⊢ nativeNoZero e 🡘 ∼mappedNativeRefutation embedding :=
  comparison_of_pra e (by
    simpa only [LogicalConnective.HomClass.map_neg] using
      PRAExpressionZFCStrict.comparison_of_bridge e hp)

end DiophantineConsistency.IPRAExpressionNative
