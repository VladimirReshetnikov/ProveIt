import DiophantineConsistency.DirectScalarEnumerator
import DiophantineConsistency.ScalarPROptimizer
import DiophantineConsistency.ZFCFromProgram
import DiophantineConsistency.CompactedJones

/-!
# A closed executable nine-variable consistency equation

`expression` is a concrete arithmetic-syntax value, built from the literal
six-register refutation enumerator. Every data stage is executable. There
is no input program, representation, compiler-correctness premise, or
consistency assumption in its final correctness theorems.

The variables range over the natural numbers, including zero. The equation
does not decide consistency; its complete zero set represents syntactic
inconsistency. The separate object-language ZFC derivation is not asserted.
-/

namespace DiophantineConsistency.ExplicitZFC

open SetTheory LeanProofs.BoundedZFCConsistency

/-- The supplied literal enumerator program, simplified with a proved
all-input evaluation identity before Diophantine compilation. -/
def program : ScalarPRCode.Realizes haltingTest := DirectEnumerator.program.optimize

/-- Explicit closed representation data for actual syntactic ZFC refutability. -/
def representation : Rep Empty (fun _ => BProv ZFCax_s [] Form.fBot) :=
  ZFCFromProgram.refutationRep program

/-- The exact natural witness count of the simplified intermediate quartic. -/
def sourceWitnessCount : ℕ := CompactedJones.witnessCount representation

theorem sourceWitnessCount_le :
    sourceWitnessCount ≤ (QuarticCompiler.compile representation).ν :=
  CompactedJones.witnessCount_le representation

/-- The requested equation: evaluate this fixed integer arithmetic syntax
at nine natural numbers and set its value equal to zero. -/
def expression : Expr (Fin 9) := CompactedJones.expression representation

/-- The ordinary integer polynomial denoted by the executable equation.
Only the Mathlib interpretation, not its coefficient recipe, is noncomputable. -/
noncomputable def polynomial : MvPolynomial (Fin 9) ℤ := expression.toPolynomial

theorem eval_polynomial (v : Fin 9 → ℤ) :
    MvPolynomial.eval v polynomial = expression.eval v :=
  Expr.eval_toPolynomial expression v

theorem syntax_hasZero_iff_refutation :
    (∃ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔
      BProv ZFCax_s [] Form.fBot :=
  CompactedJones.expression_correct representation

theorem hasNaturalZero_iff_refutation :
    HasNaturalZero polynomial ↔ BProv ZFCax_s [] Form.fBot := by
  simpa only [HasNaturalZero, eval_polynomial] using syntax_hasZero_iff_refutation

/-- Closed, unconditional correctness of the executable consistency equation. -/
theorem noSyntaxZero_iff_conZFC :
    (¬ ∃ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔ ConZFC :=
  not_congr syntax_hasZero_iff_refutation

/-- Closed, unconditional correctness of the ordinary polynomial. -/
theorem noNaturalZero_iff_conZFC : (¬ HasNaturalZero polynomial) ↔ ConZFC :=
  not_congr hasNaturalZero_iff_refutation

theorem forall_nonzero_iff_conZFC :
    (∀ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) ≠ 0) ↔ ConZFC := by
  simpa only [not_exists] using noSyntaxZero_iff_conZFC

#print axioms noSyntaxZero_iff_conZFC
#print axioms noNaturalZero_iff_conZFC

end DiophantineConsistency.ExplicitZFC
