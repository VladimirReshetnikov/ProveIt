import IPRADerivations.Core.Powers

/-! Imported from the packet `analysis/quantum_ipra_2026-11-20`, `lean/ResolventTail.lean`: the namespace is placed under `LeanProofs.IPRA` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! The finite geometric tail bound in the imaginary-resolvent construction.
After clearing denominators the statement is a natural-number inequality,
proved by quantifier-free induction in the object calculus. -/

namespace LeanProofs.IPRA.Analysis.Quantum.ResolventTail
open_ipra

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- Write s = a+b. The formula reads a^k(s+kb) ≤ s^k s. -/
def bound (k a b : PTm n) : Fm PTm n :=
  le (pw a k * ((a+b)+k*b)) (pw (a+b) k * (a+b))

private theorem start (a b : PTm n) : Γ ⊢[PRAAx] bound zero a b := by
  unfold bound
  apply le_of_eq_add (d := zero)
  apply deriveNat
  ipra_simps
  rw [natEq (pw_zero a (Γ := Γ)), natEq (pw_zero (a+b) (Γ := Γ))]
  ring

private theorem advance (k a b : PTm n) (h : Γ ⊢[PRAAx] bound k a b) :
    Γ ⊢[PRAAx] bound (succ k) a b := by
  unfold bound at *
  have hs := mul_le_mul_right (a+b) h
  have first : Γ ⊢[PRAAx] le (pw a (succ k) * ((a+b)+succ k*b))
      ((pw a k * ((a+b)+k*b))*(a+b)) := by
    apply le_of_eq_add (d := pw a k*b*b*succ k)
    have ha := natEq (pw_succ a k (Γ := Γ))
    apply deriveNat
    ipra_simps
    rw [ha]
    ring
  have last : Γ ⊢[PRAAx]
      (pw (a+b) k*(a+b))*(a+b) ≐ pw (a+b) (succ k)*(a+b) :=
    congrMul (pw_succ (a+b) k).eqSymm (.eqRefl _)
  exact le_trans first (le_congr (.eqRefl _) last hs)

private abbrev invariant : Fm PTm 3 := bound (var 0) (var 1) (var 2)

theorem open_bound : ([] : List (Fm PTm 3)) ⊢[PRAAx] invariant := by
  refine ind _ (le_QF _ _) ?_ ?_
  · unfold invariant bound
    pw_subst
    exact start _ _
  · unfold invariant bound
    pw_subst
    exact advance _ _ _ Prf.hyp0

def sentence : Fm PTm 0 := univ 3 invariant

theorem closed_bound : [] ⊢[PRAAx] sentence := closeUniv 3 open_bound

end LeanProofs.IPRA.Analysis.Quantum.ResolventTail
