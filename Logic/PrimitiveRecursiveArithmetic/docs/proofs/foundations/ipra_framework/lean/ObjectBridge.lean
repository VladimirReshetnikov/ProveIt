import ObjectKernel

/-!
# Object-theory endpoint for finite contracts

Target dependency: VladimirReshetnikov/ProveIt,
commit 42c64ff3a9f56f2a9edc1525e75ece3b720c7f77, Lean 4.32.0.

These declarations are a small standalone adapter, not a completed Booleanization or
program-verification compiler.  A record's proof fields are obligations:
declaring the record never manufactures instances of them.
-/

namespace LeanProofs.ConciseIPRA.FiniteContracts

open Syn
open scoped Fm

def one {n : Nat} : PTm n := PTm.succ PTm.zero

/-- The object formula asserting that a fixed PR Boolean test accepts. -/
def accepts {n : Nat} (test : PR n) : Fm PTm n :=
  PTm.app test Syn.var ≐ one

theorem accepts_qf {n : Nat} (test : PR n) : (accepts test).QF := trivial

/-- A bounded formula together with its *object-theory* Booleanization proof. -/
structure Booleanized (n : Nat) where
  formula : Fm PTm n
  test : PR n
  equivalent : [] ⊢[PRAAx] Fm.iff formula (accepts test)

theorem Booleanized.toTest {n : Nat} (b : Booleanized n)
    {Γ : List (Fm PTm n)} (h : Γ ⊢[PRAAx] b.formula) :
    Γ ⊢[PRAAx] accepts b.test :=
  Prf.iffMp b.equivalent.ofNil h

theorem Booleanized.fromTest {n : Nat} (b : Booleanized n)
    {Γ : List (Fm PTm n)} (h : Γ ⊢[PRAAx] accepts b.test) :
    Γ ⊢[PRAAx] b.formula :=
  Prf.iffMpr b.equivalent.ofNil h

/-- A fixed PR witness, with its derivation from the advertised precondition.
The postcondition has output at variable zero, then the `n` input variables. -/
structure Contract (n : Nat) where
  pre : Fm PTm n
  program : PR n
  post : Fm PTm (n + 1)
  certified : [pre] ⊢[PRAAx]
    post.subst (inst (PTm.app program Syn.var))

theorem Contract.existsOutput {n : Nat} (c : Contract n) :
    [c.pre] ⊢[PRAAx] Fm.ex c.post :=
  Prf.exI (PTm.app c.program Syn.var) c.certified

theorem Contract.asImplication {n : Nat} (c : Contract n) :
    [] ⊢[PRAAx] (c.pre ⟶ Fm.ex c.post) :=
  Prf.impI c.existsOutput

/-- The exact induction interface needed by the paper's bounded-loop rule. -/
structure InductionCertificate {n : Nat} (Γ : List (Fm PTm n)) where
  invariant : Fm PTm (n + 1)
  quantifierFree : invariant.QF
  base : Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: Γ.map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (Syn.var 0)))

theorem InductionCertificate.conclude {n : Nat} {Γ : List (Fm PTm n)}
    (c : InductionCertificate Γ) : Γ ⊢[PRAAx] Fm.all c.invariant :=
  PRA.qfInd c.invariant c.quantifierFree c.base c.step

end LeanProofs.ConciseIPRA.FiniteContracts
