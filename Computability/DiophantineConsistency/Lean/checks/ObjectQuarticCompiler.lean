import DiophantineConsistency.ObjectQuarticCompiler

open DiophantineConsistency
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

-- This is an actual unconditional object-ZFC proof, rather than merely a
-- correctness implication at external numeral assignments.
example (e : Expr (Fin 3)) :
    BProv ZFCax_s [] (ObjectQuarticCompiler.compilerSentence e) :=
  ObjectQuarticCompiler.zfc_proves_compiler e

-- The syntax-to-polynomial link uses the same stored quartic expression.
example (e : Expr (Fin 3)) :
    (ObjectQuarticCompiler.compiledExpression e).toPolynomial.totalDegree ≤ 4 :=
  ObjectQuarticCompiler.compiled_degree_le_four e

#print axioms Expr.SemiringZero
#print axioms Expr.splitNatural_eval_rename
#print axioms Expr.semiringZero_rename
#print axioms Expr.semiringZero_var_nat
#print axioms Expr.semiringZero_var_var
#print axioms Expr.semiringZero_var_add
#print axioms Expr.semiringZero_var_mul
#print axioms QuarticCompiler.Gates.semiringValues
#print axioms QuarticCompiler.Gates.semiringValues_root
#print axioms QuarticCompiler.Gates.semiring_complete
#print axioms QuarticCompiler.Gates.semiring_sound
#print axioms QuarticCompiler.residuals_sound
#print axioms QuarticCompiler.residuals_complete
#print axioms QuarticCompiler.exists_residuals_iff
#print axioms ObjectQuarticCompiler.expression_zero_iff
#print axioms ObjectQuarticCompiler.exists_expression_zero_iff
#print axioms ObjectQuarticCompiler.compiled_degree_le_four
#print axioms ObjectQuarticCompiler.exists_compiled_zero_iff
#print axioms ObjectQuarticCompiler.noZeroRel_compiled_iff
#print axioms ObjectQuarticCompiler.sentence_compilerSentence
#print axioms ObjectQuarticCompiler.zfc_proves_compiler
