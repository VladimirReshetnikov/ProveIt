import DiophantineConsistency.Sign14Positive74ObjectGuardedSubst

/-! SOURCE-ONLY: specialize guarded substitution to the actual expression equality matrix. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectMatrixGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero IPRANativeTheory
open IPRATheoryHilbertBridge Sign14Positive74ObjectGuardedSubst

def equalityMatrix (e : Expr (Fin 14)) : Semisentenceᵢ language 14 :=
  Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]

def guardedContrapositive (e : Expr (Fin 14)) (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢!
      ((Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard) 🡒
        (∼(Rew.embSubsts (predSuccVec v) ▹ equalityMatrix e) 🡒
          ∼(Rew.embSubsts v ▹ equalityMatrix e))) :=
  Entailment.C_trans (guardedSubstitution (equalityMatrix e) v) Entailment.CCCNN
end DiophantineConsistency.Sign14Positive74ObjectMatrixGuard
#print axioms DiophantineConsistency.Sign14Positive74ObjectMatrixGuard.guardedContrapositive
