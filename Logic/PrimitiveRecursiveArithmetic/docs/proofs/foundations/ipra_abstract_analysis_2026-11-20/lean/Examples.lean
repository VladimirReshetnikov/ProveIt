import QuantitativeKernel

namespace IPRAAbstractAnalysis.Examples

/-- For every x in {0,1,2} there exists y with x ≤ y. -/
def boundedOrder : PosFormula Unit := .all (.ex (.atom ()))

def orderAtom (_ : Unit) (ρ : Env (Fin 3)) : Bool := decide (ρ 1 ≤ ρ 0)

example : eval 3 orderAtom boundedOrder (fun _ => 0) = true := by decide

/-- The evaluator theorem turns the executable result into the logical statement. -/
example : Holds (fun a ρ => orderAtom a ρ = true) boundedOrder (fun _ => 0) :=
  (eval_correct 3 orderAtom boundedOrder (fun _ => 0)).mp (by decide)

/-- δ=1/2, λ=1/4, h=2, C=1, R=1, n=0 give k=4 and N=8. -/
def demoError : Nat → Rat
  | 0 => 1
  | j + 1 => (1 / 2 : Rat) * demoError j + (1 / 32 : Rat)

example : demoError 8 ≤ (1 / 4 : Rat) := by
  have step : ∀ j, demoError (j + 1) ≤ (1 - (1 / 2 : Rat)) * demoError j +
      2 * (1 / 4 : Rat) * (1 / 2 : Rat) ^ (0 + 3 + 1) := by
    intro j
    rw [demoError]
    grind
  have result := solver_budget (δ := (1 / 2 : Rat)) (lam := (1 / 4 : Rat))
    (by grind) (by grind) 2 1 1 0 (by grind) (by grind) demoError
    (by simp [demoError]) step
  grind

end IPRAAbstractAnalysis.Examples
