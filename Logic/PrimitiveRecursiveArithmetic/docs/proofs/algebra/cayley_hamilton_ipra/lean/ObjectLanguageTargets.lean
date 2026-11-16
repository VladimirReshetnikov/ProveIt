import ConciseIPRA.NativeBiInterpretation

/-!
Object-language interface for the Cayley--Hamilton packet.

STATUS: source outline, not compiled in the delivery environment.
Names and argument shapes were inspected at ProveIt commit
73e6a339db7c72c6b13259059a8345b24385f6e3.

This file defines a TARGET FACTORY. Its argument must eventually be the
particular PR code for the explicit finite checker described in
FORMALIZATION_PLAN.md. No such code or derivation is asserted to exist
by the definitions here. The final proof remains a formalization task.

In particular, there is no `axiom`, `sorry`, or host-to-iPRA reflection
principle in this file.
-/

namespace CayleyHamiltonObjectTargets

open LeanProofs.ConciseIPRA

/-- Universal closure of the numerical equation `check(n) = 1`.
The input `check` is a fixed unary PR program, not a code to be evaluated
by an alleged universal primitive recursive evaluator. -/
def checkStatement (check : PR 1) : Fm PTm 0 :=
  Fm.all (Fm.eq
    (PTm.app check (fun _ : Fin 1 => PTm.var 0))
    (PTm.succ PTm.zero))

/-- The completed development must inhabit this proposition for its
explicitly constructed `chCheck : PR 1`. -/
def MainDerivationTarget (check : PR 1) : Prop :=
  Prf PRAAx [] (checkStatement check)

/-- Existing repository bridge, applicable only after an object-language
derivation has actually been supplied. -/
theorem native_of_ipra (φ : Fm PTm 0) (h : Prf PRAAx [] φ) :
    NPrf [] (NFm.ofPRA φ) := by
  have h' := (pra_iff_native (Γ := []) (φ := φ)).mp h
  simpa using h'

/-- A precise final interface for transfer to the native scalar calculus. -/
theorem nativeMain_of_derivation (check : PR 1)
    (h : MainDerivationTarget check) :
    NPrf [] (NFm.ofPRA (checkStatement check)) :=
  native_of_ipra _ h

end CayleyHamiltonObjectTargets
