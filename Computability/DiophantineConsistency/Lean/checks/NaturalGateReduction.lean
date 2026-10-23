import DiophantineConsistency.SimplifiedJones

open DiophantineConsistency

-- Removing signed-splitting zeros reduces the actual quartic witness count.
def tautology : Rep Empty (fun _ => True) :=
  (Rep.equality (0 : Expr Empty) 0).ofIff (fun _ => by simp)

example : (QuarticCompiler.compile tautology).ν = 7 := rfl
example : SimplifiedJones.witnessCount tautology = 3 := rfl
example : Jones1982.Lexp (QuarticCompiler.compile tautology).ν 4 = 390625 := rfl
example : Jones1982.Lexp (SimplifiedJones.witnessCount tautology) 4 = 625 := rfl

-- The size proofs and all-input semantic proof apply to every supplied Rep.
#print axioms NatExpr.eval_simplify
#print axioms SimplifiedJones.witnessCount_le
#print axioms SimplifiedJones.noZero_expression
