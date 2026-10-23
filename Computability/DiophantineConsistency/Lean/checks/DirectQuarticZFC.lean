import DiophantineConsistency.DirectQuarticZFC

open DiophantineConsistency

private def impossible : Rep Empty (fun _ => False) :=
  (Rep.equality (Expr.constant 1 : Expr Empty) (Expr.constant 0)).ofIff
    (fun _ => by norm_num [Expr.eval])

-- The exact count includes both constant gates and the normalization guard.
example : ClosedQuartic.variableCount impossible = 3 := rfl

example : (ClosedQuartic.expression impossible).binaryOps ≤ 24 :=
  ClosedQuartic.binaryOps_le_six_mul_variables impossible

#print axioms ClosedQuartic.eval_expression
#print axioms ClosedQuartic.eval_polynomial
#print axioms ClosedQuartic.polynomial_expression
#print axioms ClosedQuartic.degree_le_four
#print axioms ClosedQuartic.variableCount_eq
#print axioms ClosedQuartic.binaryOps_le
#print axioms ClosedQuartic.binaryOps_le_six_mul_variables
#print axioms ClosedQuartic.hasSyntaxZero_iff
#print axioms ClosedQuartic.hasNaturalZero_iff
#print axioms ClosedQuartic.noNaturalZero_iff
#print axioms DirectQuarticZFC.eval_polynomial
#print axioms DirectQuarticZFC.degree_le_four
#print axioms DirectQuarticZFC.polynomial_expression
#print axioms DirectQuarticZFC.variableCount_eq
#print axioms DirectQuarticZFC.binaryOps_le
#print axioms DirectQuarticZFC.hasNaturalZero_iff_refutation
#print axioms DirectQuarticZFC.noNaturalZero_iff_conZFC
#print axioms DirectQuarticZFC.noSyntaxZero_iff_conZFC
