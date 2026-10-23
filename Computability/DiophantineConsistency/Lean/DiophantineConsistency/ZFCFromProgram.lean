import DiophantineConsistency.Bridge
import DiophantineConsistency.ComputationRepresentation
import DiophantineConsistency.ScalarPRRepresentation
import DiophantineConsistency.EquationFromRep
import DiophantineConsistency.ExecutableJones

/-!
# A consistency equation from supplied refutation-program data

The input is a concrete program paired with its evaluation theorem for
`haltingTest`. Every later representation and polynomial is constructed
from those supplied data. The separately checked program extraction must
still supply this input; this module makes no claim to extract it from a
proposition-valued computability proof.
-/

namespace DiophantineConsistency.ZFCFromProgram

open SetTheory LeanProofs.BoundedZFCConsistency

/-- Compile the actual bounded-refutation computation and fix its accepted
output to one, retaining finite syntax data throughout. -/
def refutationRep (program : ScalarPRCode.Realizes haltingTest) :
    Rep Empty (fun _ => BProv ZFCax_s [] Form.fBot) :=
  (GraphRep.existsValue program.graphRep 1).ofIff
    (fun _ => exists_haltingTest_eq_one_iff_refutation)

/-- Executable syntax construction, with every coefficient specified by the
supplied program and finite integer arithmetic. -/
def executableExpression (program : ScalarPRCode.Realizes haltingTest) : Expr (Fin 9) :=
  ExecutableJones.fromRep (refutationRep program)

theorem noExecutableZero_iff_conZFC (program : ScalarPRCode.Realizes haltingTest) :
    (¬ ∃ v : Fin 9 → ℕ,
      (executableExpression program).eval (fun i => (v i : ℤ)) = 0) ↔ ConZFC :=
  ExecutableJones.noZero_fromRep (refutationRep program)

/-- The Jones equation specified from the supplied checked program. -/
noncomputable def equation (program : ScalarPRCode.Realizes haltingTest) :
    EquationFromRep.Result (BProv ZFCax_s [] Form.fBot) :=
  EquationFromRep.construct (refutationRep program)

/-- No consistency or compiler-correctness premise is needed beyond the
supplied program data and its checked evaluation specification. -/
theorem noNaturalZero_iff_conZFC (program : ScalarPRCode.Realizes haltingTest) :
    (¬ HasNaturalZero (equation program).polynomial) ↔ ConZFC :=
  EquationFromRep.noNaturalZero_construct (refutationRep program)

theorem noSyntaxZero_iff_conZFC (program : ScalarPRCode.Realizes haltingTest) :
    (¬ ∃ v : Fin 9 → ℕ,
      (equation program).expression.eval (fun i => (v i : ℤ)) = 0) ↔ ConZFC :=
  EquationFromRep.noSyntaxZero_construct (refutationRep program)

theorem eval_expression (program : ScalarPRCode.Realizes haltingTest) (v : Fin 9 → ℤ) :
    (equation program).expression.eval v =
      MvPolynomial.eval v (equation program).polynomial :=
  EquationFromRep.eval_expression_construct (refutationRep program) v

/-- The executable syntax agrees at every integer tuple with the specified
ordinary polynomial, rather than only sharing its natural solvability. -/
theorem eval_executableExpression (program : ScalarPRCode.Realizes haltingTest) (v : Fin 9 → ℤ) :
    (executableExpression program).eval v =
      MvPolynomial.eval v (equation program).polynomial :=
  ExecutableJones.eval_fromRep_polynomial (refutationRep program) v

end DiophantineConsistency.ZFCFromProgram
