import ObjectIteration

/-! A closed use of the derived object-iPRA rule: iterated successor counts
its own steps. This exercises the actual recursion argument convention and
state/time substitution, not host evaluation of a natural-number program. -/

namespace LeanProofs.ConciseIPRA.LocalGlobal

open Syn
open scoped Fm

def countStep : PR 2 := PR.comp PR.succ (fun _ : Fin 1 => PR.proj (1 : Fin 2))

def countInvariant : Fm PTm 2 := (var 0 : PTm 2) ≐ var 1

theorem countStepCorrect :
    [countInvariant] ⊢[PRAAx] nextFormula countStep countInvariant := by
  let args : Fin 2 → PTm 2 :=
    Fin.cases (var 1) (Fin.cases (var 0) (fun i : Fin 0 => var i.succ.succ))
  have h₁ := PRA.comp (Γ := [countInvariant]) PR.succ
    (fun _ : Fin 1 => PR.proj (1 : Fin 2)) args
  have h₂ := PRA.proj (Γ := [countInvariant]) (1 : Fin 2) args
  have h₃ := Prf.eqCongr1 (PTm.succ (var 0)) h₂
  have h₄ := Prf.eqCongr1 (PTm.succ (var 0))
    (Prf.hyp0 : [countInvariant] ⊢[PRAAx] (var 0 : PTm 2) ≐ var 1)
  have e : [countInvariant] ⊢[PRAAx]
      PTm.app countStep args ≐ PTm.succ (var 1 : PTm 2) := by
    exact Prf.eqTrans h₁ (Prf.eqTrans h₃ h₄)
  simpa [nextFormula, countInvariant, instStateTime, args] using e

theorem counting_is_time : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    Fm.all (runInvariant PR.zero countStep countInvariant) := by
  apply primitiveRecursionInvariant PR.zero countStep countInvariant
    (by trivial) []
  · have he : (var : Fin 0 → PTm 0) = Fin.elim0 := funext fun i => i.elim0
    simpa [baseFormula, countInvariant, instStateTime, PTm.zero, he] using
      (Prf.eqRefl (Ax := PRAAx) (Γ := ([] : List (Fm PTm 0))) (PTm.zero : PTm 0))
  · exact countStepCorrect

end LeanProofs.ConciseIPRA.LocalGlobal
