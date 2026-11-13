import DiophantineConsistency.Current14Carrier65DegreeExpression
import DiophantineConsistency.Sign17ExactDegree

/-! Candidate exact degree for the maintained in-Lean current expression. -/
namespace DiophantineConsistency.Current14Carrier65DegreeExpressionCurrent

theorem current_expression_exact :
    (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports).toPolynomial.totalDegree = 150 :=
  Current14Carrier65DegreeExpression.expression_exact CurrentWindowCarry2011.ports
    Sign17ExactDegree.current_port_nonzero

end DiophantineConsistency.Current14Carrier65DegreeExpressionCurrent

#print axioms DiophantineConsistency.Current14Carrier65DegreeExpressionCurrent.current_expression_exact
