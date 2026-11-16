import ConciseIPRA.PR

/-!
# Object-iPRA glue for finite certificates and stable observables

STATUS: compiled with Lean 4.32.0 against the exact source interfaces at
ProveIt commit c39c388d4f87220ab9e758ae457520bbc0d74341. The axiom audit
reports only `propext` and `Quot.sound`; no `sorry` or added axioms occur.
These are inference-rule
combinators; none proves the Jacobi arithmetic estimates by itself.

Every conclusion has the actual embedded `Prf PRAAx` type. In particular,
semantic Lean proofs are not silently converted into object derivations.
-/

namespace LeanProofs.ConciseIPRA.ObservableGlue

open Syn
open scoped Fm

variable {n : Nat} {Gamma : List (Fm PTm n)}

/-- The numerical predicate that a fixed PR Boolean checker returns one. -/
def checkFormula {r : Nat} (check : PR r) (xs : Fin r -> PTm n) : Fm PTm n :=
  PTm.app check xs ≐ PTm.succ PTm.zero

/-- Specialize an allowed quantifier-free induction at a specified fuel.
The context is fixed during induction and may contain quantified formulas.
The invariant itself must genuinely be quantifier-free. -/
theorem boundedInvariantAt
    (I : Fm PTm (n + 1)) (hI : I.QF) (fuel : PTm n)
    (h0 : Gamma ⊢[PRAAx] I.subst (inst PTm.zero))
    (hS : I :: Gamma.map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0)))) :
    Gamma ⊢[PRAAx] I.subst (inst fuel) :=
  Prf.allE fuel (PRA.qfInd I hI h0 hS)

/-- A finite loop produces a certificate once its terminal invariant
has a proved certificate extraction rule. The actual extraction estimate
is supplied as an object proof, not as a truth-valued assertion. -/
theorem loopProducesCertificate
    (I : Fm PTm (n + 1)) (hI : I.QF) (fuel : PTm n)
    (C : Fm PTm n)
    (h0 : Gamma ⊢[PRAAx] I.subst (inst PTm.zero))
    (hS : I :: Gamma.map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0))))
    (hfinish : Gamma ⊢[PRAAx] (I.subst (inst fuel) ⟶ C)) :
    Gamma ⊢[PRAAx] C :=
  Prf.impE hfinish (boundedInvariantAt I hI fuel h0 hS)

/-- Correctness of two independent certificates plus a proved stability
estimate for their observations. No equality or compatibility between
the certificate witnesses is assumed. -/
theorem observableOfIndependentCertificates
    (C1 C2 O : Fm PTm n)
    (h1 : Gamma ⊢[PRAAx] C1)
    (h2 : Gamma ⊢[PRAAx] C2)
    (hstable : Gamma ⊢[PRAAx] (C1 ⟶ C2 ⟶ O)) :
    Gamma ⊢[PRAAx] O :=
  Prf.impE (Prf.impE hstable h1) h2

/-- The same rule with stability proved under local assumptions. -/
theorem observableFromLocalStability
    (C1 C2 O : Fm PTm n)
    (h1 : Gamma ⊢[PRAAx] C1)
    (h2 : Gamma ⊢[PRAAx] C2)
    (hstable : C1 :: C2 :: Gamma ⊢[PRAAx] O) :
    Gamma ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI hstable)) h2) h1

/-- A typical end-to-end use: two bounded finite computations, possibly
at unrelated precisions and with entirely different witnesses, yield
an object-theory relation between their compressed observations. -/
theorem twoLoopsStableObservable
    (I1 I2 : Fm PTm (n + 1)) (qf1 : I1.QF) (qf2 : I2.QF)
    (fuel1 fuel2 : PTm n) (C1 C2 O : Fm PTm n)
    (base1 : Gamma ⊢[PRAAx] I1.subst (inst PTm.zero))
    (step1 : I1 :: Gamma.map Fm.shift ⊢[PRAAx]
      I1.subst (repl (PTm.succ (var 0))))
    (base2 : Gamma ⊢[PRAAx] I2.subst (inst PTm.zero))
    (step2 : I2 :: Gamma.map Fm.shift ⊢[PRAAx]
      I2.subst (repl (PTm.succ (var 0))))
    (finish1 : Gamma ⊢[PRAAx] (I1.subst (inst fuel1) ⟶ C1))
    (finish2 : Gamma ⊢[PRAAx] (I2.subst (inst fuel2) ⟶ C2))
    (stability : C1 :: C2 :: Gamma ⊢[PRAAx] O) :
    Gamma ⊢[PRAAx] O :=
  observableFromLocalStability C1 C2 O
    (loopProducesCertificate I1 qf1 fuel1 C1 base1 step1 finish1)
    (loopProducesCertificate I2 qf2 fuel2 C2 base2 step2 finish2)
    stability

end LeanProofs.ConciseIPRA.ObservableGlue
