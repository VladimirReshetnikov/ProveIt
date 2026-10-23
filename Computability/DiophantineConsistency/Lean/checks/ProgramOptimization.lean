import DiophantineConsistency.ScalarPROptimizer

open DiophantineConsistency
open ScalarPRCode

-- A complete recursion trace for an unchanged accumulator is eliminated.
example (base : ScalarPRCode) :
    (prec base (comp right right)).optimize.eval =
      fun n => base.eval n.unpair.1 := by
  funext n
  rw [eval_optimize]
  simp only [eval, Nat.unpair_pair]
  induction n.unpair.2 <;> simp_all

-- A seven-instruction recursive counter becomes one inverse projection.
def counter : ScalarPRCode := prec zero (comp succ (comp right right))

example : counter.optimize = right := rfl
example : counter.nodeCount = 7 := rfl
example : counter.optimize.nodeCount = 1 := rfl
example (n : ℕ) : counter.eval n = n.unpair.2 := by
  rw [← eval_optimize]
  rfl

#print axioms ScalarPRCode.eval_optimize
#print axioms ScalarPRCode.nodeCount_optimize_le
