import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# FRNF kernel-facing logical layer

This file is intended to live inside the ProveIt root workspace, against
Lean 4.32.0 and the current `ConciseIPRA` library.  It contains the generic
logical composition layer only: a proof schedule, quantifier-free loop
closure, boundary discharge, stable-observer composition, and native export.

There are no `axiom` declarations and no `sorry` placeholders in this file.
It was source-audited against the repository API, but Lean was not installed
in the artifact environment, so a pinned `lake build` remains required.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FRNF

open Syn
open scoped Fm

/-- A finite reverse-topological schedule of object-iPRA derivations. -/
structure Schedule {n : Nat}
    (Γ : List (Fm PTm n)) (done : List (Fm PTm n)) where
  derive : ∀ A, A ∈ done → Γ ⊢[PRAAx] A

namespace Schedule

variable {n : Nat} {Γ : List (Fm PTm n)}
variable {done deps : List (Fm PTm n)} {A : Fm PTm n}

/-- Empty proof schedule. -/
def empty : Schedule Γ [] where
  derive := by
    intro C hC
    simp at hC

/-- Retrieve a previously compiled node. -/
theorem get (s : Schedule Γ done) (hA : A ∈ done) :
    Γ ⊢[PRAAx] A :=
  s.derive A hA

/--
Add a node proved from a declared dependency sublist and the permanent base
context.  `Prf.trans` performs simultaneous cut; the inclusion proof is the
acyclicity certificate.
-/
def extend (s : Schedule Γ done)
    (hdeps : deps ⊆ done)
    (local : deps ++ Γ ⊢[PRAAx] A) :
    Schedule Γ (A :: done) where
  derive := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hOld
    · exact local.trans (fun D hD => by
        rcases List.mem_append.mp hD with hDep | hBase
        · exact s.derive D (hdeps hDep)
        · exact Prf.hyp hBase)
    · exact s.derive C hOld

/-- A three-node regression pattern for generated proof terms. -/
theorem compileThree
    {A B C : Fm PTm n}
    (hA : Γ ⊢[PRAAx] A)
    (hB : A :: Γ ⊢[PRAAx] B)
    (hC : B :: A :: Γ ⊢[PRAAx] C) :
    Γ ⊢[PRAAx] C := by
  let s0 : Schedule Γ [] := Schedule.empty
  let s1 : Schedule Γ [A] := Schedule.extend s0 (by simp) (by simpa using hA)
  let s2 : Schedule Γ [B, A] := Schedule.extend s1 (by simp) (by simpa using hB)
  let s3 : Schedule Γ [C, B, A] := Schedule.extend s2 (by simp) (by simpa using hC)
  exact s3.get (by simp)

end Schedule

/-- A clocked loop with an actual quantifier-free object invariant. -/
structure QFLoop {n : Nat} (Γ : List (Fm PTm n)) where
  invariant : Fm PTm (n + 1)
  qf : invariant.QF
  base : Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: Γ.map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (var 0)))

namespace QFLoop

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- Close the loop by the one induction principle allowed in iPRA. -/
theorem close (c : QFLoop Γ) :
    Γ ⊢[PRAAx] Fm.all c.invariant :=
  PRA.qfInd c.invariant c.qf c.base c.step

/-- Specialize the closed invariant at an explicit fuel term. -/
theorem at (c : QFLoop Γ) (fuel : PTm n) :
    Γ ⊢[PRAAx] c.invariant.subst (inst fuel) :=
  Prf.allE fuel c.close

/-- Extract an arbitrary conclusion from the terminal invariant. -/
theorem finish (c : QFLoop Γ) (fuel : PTm n) (Goal : Fm PTm n)
    (terminal : c.invariant.subst (inst fuel) :: Γ ⊢[PRAAx] Goal) :
    Γ ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impI terminal) (c.at fuel)

end QFLoop

/-- Combine two independently produced certificates through a stable observer. -/
theorem stablePair
    {n : Nat} {Γ : List (Fm PTm n)}
    (C₁ C₂ Goal : Fm PTm n)
    (h₁ : Γ ⊢[PRAAx] C₁)
    (h₂ : Γ ⊢[PRAAx] C₂)
    (stable : C₁ :: C₂ :: Γ ⊢[PRAAx] Goal) :
    Γ ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI stable)) h₂) h₁

/-- Simultaneous-cut form of a finite stable observer. -/
theorem stableMany
    {n : Nat} {Γ Δ : List (Fm PTm n)} {Goal : Fm PTm n}
    (local : Δ ⊢[PRAAx] Goal)
    (certified : ∀ A ∈ Δ, Γ ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] Goal :=
  local.trans certified

/-- Keep a deep or externally supplied producer theorem visible as a boundary. -/
theorem dischargeBoundary
    {n : Nat} {Γ : List (Fm PTm n)}
    (Boundary Goal : Fm PTm n)
    (hBoundary : Γ ⊢[PRAAx] Boundary)
    (body : Boundary :: Γ ⊢[PRAAx] Goal) :
    Γ ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impI body) hBoundary

/-- Exact branch collapse is guarded by an explicit separation/gap certificate. -/
theorem exactUnderGap
    {n : Nat} {Γ : List (Fm PTm n)}
    (Approx Gap Exact : Fm PTm n)
    (hApprox : Γ ⊢[PRAAx] Approx)
    (hGap : Γ ⊢[PRAAx] Gap)
    (collapse : Approx :: Gap :: Γ ⊢[PRAAx] Exact) :
    Γ ⊢[PRAAx] Exact :=
  stablePair Approx Gap Exact hApprox hGap collapse

/-- Transfer a completed ordinary-iPRA derivation to the native scalar core. -/
def exportNative
    {n : Nat} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) :
    NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

end LeanProofs.ConciseIPRA.FRNF

#print axioms LeanProofs.ConciseIPRA.FRNF.Schedule.compileThree
#print axioms LeanProofs.ConciseIPRA.FRNF.stablePair
