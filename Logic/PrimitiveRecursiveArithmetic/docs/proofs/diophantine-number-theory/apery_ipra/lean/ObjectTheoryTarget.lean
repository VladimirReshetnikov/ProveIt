import ConciseIPRA.NativeBiInterpretation
import AperySpec

/-!
# Required object-theory target

STATUS: UNCOMPILED interface and conditional transport only. No PR compiler,
compiled checker, or completed internal Apéry derivation is supplied here.
There are no axioms or `sorry` placeholders. In particular the conditional
theorem `native_of_internal` does not assert that its hypothesis exists.

Inspected environment: ProveIt at
d72c8b24637e342816dc92d11bef337748683e51, Lean/Mathlib 4.32.0.
-/

namespace AperyIPRA.ObjectTheory

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- External numerical interpretation, used only to specify compiler agreement.
It neither proves the object theory sound nor proves the checker's result. -/
def evalPR : {k : Nat} → PR k → (Fin k → Nat) → Nat
  | _, .zero, _ => 0
  | _, .succ, xs => xs 0 + 1
  | _, .proj i, xs => xs i
  | _, .comp f gs, xs => evalPR f (fun i => evalPR (gs i) xs)
  | _, .prec f g, xs =>
      Nat.rec (evalPR f (fun i => xs i.succ))
        (fun y previous =>
          evalPR g (Fin.cases y (Fin.cases previous (fun i => xs i.succ))))
        (xs 0)

/-- Work remaining: give a concrete PR syntax tree and prove its agreement
with the fully defined natural-number specification. No inhabitant provided. -/
structure CompiledAperyProgram where
  code : PR 3
  correct : ∀ pPositive pNegative q0,
    evalPR code (Fin.cases pPositive
      (Fin.cases pNegative (Fin.cases q0 Fin.elim0))) =
      Spec.checkApery pPositive pNegative q0

/-- Under forall pPositive, forall pNegative, forall q0, the de Bruijn
indices are respectively 2, 1, 0. The program itself uses q=q0+1. -/
def checkerTerm (c : CompiledAperyProgram) : PTm 3 :=
  PTm.app c.code (Fin.cases (PTm.var 2)
    (Fin.cases (PTm.var 1) (Fin.cases (PTm.var 0) Fin.elim0)))

def aperyMatrix (c : CompiledAperyProgram) : Fm PTm 3 :=
  Fm.eq (checkerTerm c) PTm.zero

def aperyFormula (c : CompiledAperyProgram) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (aperyMatrix c)))

/-- The actual theorem that a complete formalization must construct. -/
def InternalAperyProof (c : CompiledAperyProgram) : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] aperyFormula c

/-- CONDITIONAL: the inspected bi-interpretation transports an existing
internal iPRA derivation to the concise native calculus. -/
theorem native_of_internal (c : CompiledAperyProgram)
    (h : InternalAperyProof c) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (aperyFormula c)) := by
  simpa using
    (pra_iff_native (Γ := ([] : List (Fm PTm 0)))
      (φ := aperyFormula c)).mp h

/-- Equivalent target if arithmetic is developed in the scalar presentation. -/
theorem internal_iff_scalar (c : CompiledAperyProgram) :
    InternalAperyProof c ↔
      (([] : List (Fm Tm 0)) ⊢[TeqAx]
        (aperyFormula c).map (fun _ => FromPRA.sigma)) := by
  exact pra_iff_teq (Γ := ([] : List (Fm PTm 0))) (φ := aperyFormula c)

end AperyIPRA.ObjectTheory
