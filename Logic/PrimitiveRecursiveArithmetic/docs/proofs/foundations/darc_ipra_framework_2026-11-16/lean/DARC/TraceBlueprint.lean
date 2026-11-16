import DARC.StructuralKernel
import IPRADerivations.Core.Pairing

/-! Blueprint: normalized trace reflection for fixed bounded loops. -/
namespace LeanProofs.IPRA.DARC

open LeanProofs.ConciseIPRA LeanProofs.IPRA Syn
open scoped Fm

structure TraceSpec (n : ℕ) where
  stateCode : PR n
  initial : Fin n → PTm 0
  step : Fin n → PTm n
  invariant : Fm PTm n
  invariantQF : invariant.QF

/-- Primitive-recursive state after `t` iterations, generated componentwise or
through the checked simultaneous-recursion/pairing layer. -/
def TraceSpec.run (S : TraceSpec n) : Fin n → PR 1 :=
  fun j => compileIterate S.initial S.step j

/-- One-step equations for the generated trace. -/
theorem run_zero (S : TraceSpec n) (j : Fin n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      app (S.run j) ![zero] ≐ S.initial j := by
  sorry

theorem run_succ (S : TraceSpec n) (j : Fin n) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx]
      app (S.run j) ![succ (var 0)] ≐
        S.step j |>.subst (fun i => app (S.run i) ![var 0]) := by
  sorry

/-- Quantifier-free invariant reflection. -/
theorem invariant_all (S : TraceSpec n)
    (base : ([] : List (Fm PTm 0)) ⊢[PRAAx]
      S.invariant.subst S.initial)
    (step : [S.invariant] ⊢[PRAAx]
      S.invariant.subst S.step) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx]
      S.invariant.subst (fun i => app (S.run i) ![var 0]) := by
  sorry

end LeanProofs.IPRA.DARC
