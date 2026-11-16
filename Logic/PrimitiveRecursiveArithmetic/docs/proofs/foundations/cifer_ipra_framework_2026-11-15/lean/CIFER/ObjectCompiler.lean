import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# CIFER object-language compiler core

This file is written against the current `ConciseIPRA` API.  Its purpose is
narrow: compose *actual* object-iPRA derivations.  A semantic Lean theorem is
never coerced into an arithmetic theorem.

`ResidualBuild Gamma boundary done` is a reverse-topological proof schedule.
Every formula in `done` has a derivation from `boundary ++ Gamma`.  Boundary
formulas are deliberately visible: they are the unresolved producer
obligations returned by residual compilation.  Once derivations of those
formulas are supplied, `ResidualBuild.close` discharges them by simultaneous
cut (`Prf.trans`).

The source contains no `axiom` declaration and no `sorry`.  It is an
integration-oriented outline and was not elaborated in the artifact runtime.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace CIFER

open Syn
open scoped Fm

/-- A fixed primitive-recursive Boolean checker is accepted when it returns 1. -/
def checked {r n : Nat} (check : PR r) (args : Fin r -> PTm n) : Fm PTm n :=
  PTm.app check args ≐ PTm.succ PTm.zero

@[simp] theorem checked_qf {r n : Nat} (check : PR r) (args : Fin r -> PTm n) :
    (checked check args).QF := by
  simp [checked]

/-- A proof schedule whose unresolved producer assumptions remain explicit. -/
structure ResidualBuild {n : Nat}
    (Gamma boundary done : List (Fm PTm n)) where
  derive : forall A, A ∈ done -> boundary ++ Gamma ⊢[PRAAx] A

namespace ResidualBuild

variable {n : Nat}
variable {Gamma boundary done deps : List (Fm PTm n)}
variable {A B : Fm PTm n}

/-- Empty proof schedule. -/
def nil : ResidualBuild Gamma boundary [] where
  derive := by
    intro C hC
    simp at hC

/-- Retrieve a theorem already compiled into the schedule. -/
theorem get (s : ResidualBuild Gamma boundary done) (hA : A ∈ done) :
    boundary ++ Gamma ⊢[PRAAx] A :=
  s.derive A hA

/--
Add a node whose local derivation can use every previously compiled node,
all residual boundary formulas, and the permanent input context.
-/
def step (s : ResidualBuild Gamma boundary done)
    (local : done ++ (boundary ++ Gamma) ⊢[PRAAx] A) :
    ResidualBuild Gamma boundary (A :: done) where
  derive := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hOld
    · exact local.trans (fun D hD => by
        rcases List.mem_append.mp hD with hDone | hCtx
        · exact s.derive D hDone
        · exact Prf.hyp hCtx)
    · exact s.derive C hOld

/--
Add a node from an explicit dependency sublist.  The inclusion proof is the
host-level acyclicity/topological-order certificate.
-/
def stepFrom (s : ResidualBuild Gamma boundary done)
    (hdeps : deps ⊆ done)
    (local : deps ++ (boundary ++ Gamma) ⊢[PRAAx] A) :
    ResidualBuild Gamma boundary (A :: done) where
  derive := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hOld
    · exact local.trans (fun D hD => by
        rcases List.mem_append.mp hD with hDep | hCtx
        · exact s.derive D (hdeps hDep)
        · exact Prf.hyp hCtx)
    · exact s.derive C hOld

/--
Discharge all residual producer obligations.  This is the final distinction
between a conditional framework theorem and a closed iPRA theorem.
-/
theorem close (s : ResidualBuild Gamma boundary done)
    (hA : A ∈ done)
    (supply : forall C, C ∈ boundary -> Gamma ⊢[PRAAx] C) :
    Gamma ⊢[PRAAx] A := by
  exact (s.get hA).trans (fun C hC => by
    rcases List.mem_append.mp hC with hBoundary | hGamma
    · exact supply C hBoundary
    · exact Prf.hyp hGamma)

/-- A three-node regression pattern, with one visible residual formula. -/
theorem compileThreeResidual
    {R A B C : Fm PTm n}
    (hA : R :: Gamma ⊢[PRAAx] A)
    (hB : A :: R :: Gamma ⊢[PRAAx] B)
    (hC : B :: A :: R :: Gamma ⊢[PRAAx] C) :
    R :: Gamma ⊢[PRAAx] C := by
  let s0 : ResidualBuild Gamma [R] [] := ResidualBuild.nil
  let s1 : ResidualBuild Gamma [R] [A] := ResidualBuild.step s0 (by simpa using hA)
  let s2 : ResidualBuild Gamma [R] [B, A] := ResidualBuild.step s1 (by simpa using hB)
  let s3 : ResidualBuild Gamma [R] [C, B, A] := ResidualBuild.step s2 (by simpa using hC)
  exact s3.get (by simp)

end ResidualBuild

variable {n : Nat} {Delta : List (Fm PTm n)}

/--
Specialize quantifier-free induction at arbitrary primitive-recursive fuel.
The permanent context `Delta` can include ordinary hypotheses and residual
producer assumptions.
-/
theorem invariantAt
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (fuel : PTm n)
    (base : Delta ⊢[PRAAx] I.subst (inst PTm.zero))
    (step : I :: Delta.map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0)))) :
    Delta ⊢[PRAAx] I.subst (inst fuel) :=
  Prf.allE fuel (PRA.qfInd I hI base step)

/--
Compile a bounded loop from a quantifier-free invariant and an arbitrary
terminal extractor.  The extractor may conclude a quantified formula.
-/
theorem loop
    (Q : Fm PTm n)
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (fuel : PTm n)
    (base : Delta ⊢[PRAAx] I.subst (inst PTm.zero))
    (step : I :: Delta.map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0))))
    (finish : I.subst (inst fuel) :: Delta ⊢[PRAAx] Q) :
    Delta ⊢[PRAAx] Q :=
  Prf.impE (Prf.impI finish) (invariantAt I hI fuel base step)

/-- An explicitly supplied finite witness yields the object existential. -/
theorem existsFromWitness
    (R : Fm PTm (n + 1)) (w : PTm n)
    (hw : Delta ⊢[PRAAx] R.subst (inst w)) :
    Delta ⊢[PRAAx] Fm.ex R :=
  Prf.exI w hw

/--
Two independently produced certificates determine an observable when the
comparison theorem is itself an embedded derivation.  No coherent selector of
certificates is required.
-/
theorem stableObservable
    (C1 C2 O : Fm PTm n)
    (h1 : Delta ⊢[PRAAx] C1)
    (h2 : Delta ⊢[PRAAx] C2)
    (stable : C1 :: C2 :: Delta ⊢[PRAAx] O) :
    Delta ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI stable)) h2) h1

/-- Make a nonuniform or deep producer theorem an explicit boundary. -/
theorem withBoundary
    (Boundary Goal : Fm PTm n)
    (hBoundary : Delta ⊢[PRAAx] Boundary)
    (body : Boundary :: Delta ⊢[PRAAx] Goal) :
    Delta ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impI body) hBoundary

/-- Exact branch collapse is allowed only with an explicit separation witness. -/
theorem exactFromGap
    (Approx Gap Exact : Fm PTm n)
    (hApprox : Delta ⊢[PRAAx] Approx)
    (hGap : Delta ⊢[PRAAx] Gap)
    (sound : Approx :: Gap :: Delta ⊢[PRAAx] Exact) :
    Delta ⊢[PRAAx] Exact :=
  stableObservable Approx Gap Exact hApprox hGap sound

/-- Export a completed usual-iPRA derivation to the native scalar calculus. -/
def exportNative
    {Gamma : List (Fm PTm n)} {phi : Fm PTm n}
    (h : Gamma ⊢[PRAAx] phi) :
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi) :=
  pra_iff_native.mp h

end CIFER
end LeanProofs.ConciseIPRA

#print axioms LeanProofs.ConciseIPRA.CIFER.ResidualBuild.compileThreeResidual
#print axioms LeanProofs.ConciseIPRA.CIFER.loop
#print axioms LeanProofs.ConciseIPRA.CIFER.stableObservable
