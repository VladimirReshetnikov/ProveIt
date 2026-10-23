import DiophantineConsistency.NativeGraphEnumerator
import DiophantineConsistency.CompactedJones
import DiophantineConsistency.ExplicitZFC
import DiophantineConsistency.PositiveDomain

/-!
# A closed equation from the native arithmetic graph

This alternative bypasses the generic primitive-recursive graph compiler.
Arithmetic and Cantor inversion use their supplied low-degree graph data;
only the outer enumerator iteration needs a trace. Its final equation is
again closed, executable, and correct for the actual ZFC proof predicate.
No comparison of the complete source sizes is asserted without measurement.
-/

namespace DiophantineConsistency.NativeZFC

open SetTheory LeanProofs.BoundedZFCConsistency

def representation : Rep Empty (fun _ => BProv ZFCax_s [] Form.fBot) :=
  (GraphRep.existsValue NativeGraphEnumerator.program 1).ofIff
    (fun _ => exists_haltingTest_eq_one_iff_refutation)

def sourceWitnessCount : ℕ := CompactedJones.witnessCount representation

def expression : Expr (Fin 9) := CompactedJones.expression representation

noncomputable def polynomial : MvPolynomial (Fin 9) ℤ := expression.toPolynomial

theorem syntax_hasZero_iff_refutation :
    (∃ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔
      BProv ZFCax_s [] Form.fBot :=
  CompactedJones.expression_correct representation

theorem hasNaturalZero_iff_refutation :
    HasNaturalZero polynomial ↔ BProv ZFCax_s [] Form.fBot := by
  simpa only [HasNaturalZero, polynomial, Expr.eval_toPolynomial] using syntax_hasZero_iff_refutation

theorem noNaturalZero_iff_conZFC : (¬ HasNaturalZero polynomial) ↔ ConZFC :=
  not_congr hasNaturalZero_iff_refutation

theorem noSyntaxZero_iff_conZFC :
    (¬ ∃ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔ ConZFC :=
  not_congr syntax_hasZero_iff_refutation

theorem eval_polynomial (v : Fin 9 → ℤ) :
    MvPolynomial.eval v polynomial = expression.eval v :=
  Expr.eval_toPolynomial expression v

theorem hasZero_iff_explicit :
    HasNaturalZero polynomial ↔ HasNaturalZero ExplicitZFC.polynomial :=
  hasNaturalZero_iff_refutation.trans ExplicitZFC.hasNaturalZero_iff_refutation.symm

/-- The exact shift gives another closed form on nine strictly positive integers. -/
def positiveExpression : Expr (Fin 9) := expression.positiveShift

theorem noPositiveZero_iff_conZFC :
    (¬ ∃ v : Fin 9 → ℤ, (∀ i, 0 < v i) ∧ positiveExpression.eval v = 0) ↔ ConZFC :=
  not_congr ((Expr.hasPositiveZero_positiveShift_iff _).trans syntax_hasZero_iff_refutation)

end DiophantineConsistency.NativeZFC
