import IPRAComplexity

open IPRAComplexity

example : bany (fun n => n == 7) 7 = false := by decide
example : bany (fun n => n == 7) 8 = true := by decide
example : firstWitness (fun n => decide (3 ≤ n)) 6 = some 3 := by decide

def lineGraph (u v : Nat) : Bool := v == u + 1

example : reach 6 lineGraph 2 0 5 = false := by decide
example : reach 6 lineGraph 3 0 5 = true := by decide
example : reach 6 lineGraph 3 5 0 = false := by decide
example : reach 6 lineGraph 3 6 6 = false := by decide

def sampleGates : GateSystem :=
  [(2, .conjunction 0 1), (3, .negate 2)]

def sampleAssignment : Assignment := fun i =>
  if i == 0 then true else if i == 1 then false else if i == 2 then false else true

example : CNF.eval sampleAssignment sampleGates.clauses = true := by decide
example : sampleGates.clauses.length = 5 := by decide

def p : Polynomial := .add (.mul .var .var) (.const 2)
def q : Polynomial := .mul (.const 3) .var
example : (q.subst p).eval 4 = 54 := by decide
