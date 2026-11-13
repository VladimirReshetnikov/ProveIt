import RationalCarrier64CurrentPair

/-! The integer expression used to represent the cleared 64-row evaluator
is the existing 65-operation current14 integer syntax. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ClearedCurrentIPRA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open IPRAStandardTheory IPRAFoundationZFCMappedNegation IPRACurrentNativeZFC
open ObjectCurrentEquation2011 RationalCarrier64CurrentPair

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

/-- The denominator-cleared integer representation, in existing syntax. -/
def clearedExpression : Expr (Fin 14) := expressionAt CurrentWindowCarry2011.ports

/-- The selected term is the checked normalized 65-row graph, pointwise. -/
theorem cleared_eval (v : Fin 14 → ℤ) :
    clearedExpression.eval v =
      RationalCarrier64Current.value65 CurrentWindowCarry2011.ports v :=
  (RationalCarrier64Current.value65_eq_expressionAt CurrentWindowCarry2011.ports v).symm

/-- Its positive-integer no-zero sentence, using the existing shift. -/
def clearedNoZero : Sentenceᵢ language :=
  let e := positiveShift clearedExpression
  ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

theorem clearedNoZero_eq_noZero14 : clearedNoZero = noZero14 := rfl

/-- This derivation is about the integer syntax, not rational syntax. -/
theorem cleared_ipra : standardTheory ⊢
    clearedNoZero 🡘 ∼mappedNativeRefutation embedding := by
  rw [clearedNoZero_eq_noZero14]
  exact external_and_ipra.2

#print axioms cleared_eval
#print axioms clearedNoZero_eq_noZero14
#print axioms cleared_ipra

end DiophantineConsistency.ClearedCurrentIPRA
