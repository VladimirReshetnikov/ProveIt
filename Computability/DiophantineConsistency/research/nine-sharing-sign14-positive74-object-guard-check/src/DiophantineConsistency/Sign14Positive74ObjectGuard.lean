import DiophantineConsistency.Sign14Positive74IPRAEndpoint

/-! SOURCE-ONLY: native sentence with 14 explicitly nonzero coordinates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero

/-- The guard says that each of the fourteen bound variables is nonzero. -/
def coordinateNonzero (i : Fin 14) : Semisentenceᵢ language 14 :=
  ∼(Semiformulaᵢ.rel Language.ORing.Rel.eq ![.bvar i, .func (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0])

def guard : Semisentenceᵢ language 14 :=
  ⋀ ((List.finRange 14).map coordinateNonzero)

def positiveNoZero (e : Expr (Fin 14)) : Sentenceᵢ language :=
  ∀⁰* (guard 🡒 ∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

def currentPositiveNoZero : Sentenceᵢ language :=
  positiveNoZero (Sign14Positive74.expression CurrentWindowCarry2011.ports)

theorem guard_count : ((List.finRange 14).map coordinateNonzero).length = 14 := by simp
end DiophantineConsistency.Sign14Positive74ObjectGuard
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuard.guard_count
