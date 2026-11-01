import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAErasedDefiningImages

/-! Uncompiled draft of a direct equality-only no-zero formula. Its syntax
and proof require a coherent Lean replay. It does not identify the erased
refutation predicate with any independent ZFC proof encoding. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReferenceNoZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAErasedDefiningImages
open PRATheory PRANoZeroUnary FoundationHANoZero

def noZero {n : ℕ} (e : Expr (Fin n)) : Sentenceᵢ IPRAEqualityOnlyReference.language :=
  ∀⁰* (∼(Semiformulaᵢ.rel IPRAEqualityOnlyReference.EqualityRel.eq
    ![Semiterm.lMap termsToReference
        (Semiterm.lMap PRALanguage.embedding
          (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1))),
      Semiterm.lMap termsToReference
        (Semiterm.lMap PRALanguage.embedding
          (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2)))]))

theorem erase_nativeNoZero {n : ℕ} (e : Expr (Fin n)) :
    erase (IPRAExpressionNative.nativeNoZero e) = noZero e := by
  simp only [IPRAExpressionNative.nativeNoZero, noZero, erase_allClosure,
    Semiformulaᵢ.neg_def, erase]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

end DiophantineConsistency.IPRAReferenceNoZero
