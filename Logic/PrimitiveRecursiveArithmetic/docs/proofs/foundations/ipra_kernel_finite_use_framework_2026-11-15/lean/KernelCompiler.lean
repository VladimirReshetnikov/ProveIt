import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Kernel-facing finite-use compiler for iPRA

This module contains only generic logical composition.  Every main conclusion
has the actual embedded type `Prf PRAAx`; there is no conversion from a host
Lean proposition into an object-iPRA theorem.

The central object is `ProofBuild Γ done`.  It records that every formula in a
reverse-topological list `done` has an embedded derivation from the fixed base
context `Γ`.  A new node may be added only from earlier nodes.  Consequently a
finite contract DAG can be compiled by a sequence of `ProofBuild.step` or
`ProofBuild.stepFrom` applications.

The file is source-auditable: it introduces no axiom and contains no `sorry`.
It was written against the current `ConciseIPRA.PR` interface inspected at
ProveIt main commit 9df5b64f82b891640b2154bd14dcee251a25d37f.
Compilation still has to be run in the pinned Lean 4.32.0 environment.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace KernelFiniteUse

open Syn
open scoped Fm

/-- A fixed primitive-recursive Boolean checker is true when its value is one. -/
def checked {r n : Nat} (check : PR r) (args : Fin r → PTm n) : Fm PTm n :=
  PTm.app check args ≐ PTm.succ PTm.zero

@[simp] theorem checked_qf {r n : Nat} (check : PR r) (args : Fin r → PTm n) :
    (checked check args).QF := by
  simp [checked]

/--
`ProofBuild Γ done` is a proof-carrying reverse topological schedule.
Every formula already listed in `done` is derivable from the permanent input
context `Γ`.  The formulas themselves may contain arbitrary quantifiers; only
loop invariants passed to `PRA.qfInd` must be quantifier-free.
-/
structure ProofBuild {n : Nat}
    (Γ : List (Fm PTm n)) (done : List (Fm PTm n)) where
  derive : ∀ A, A ∈ done → Γ ⊢[PRAAx] A

namespace ProofBuild

variable {n : Nat} {Γ : List (Fm PTm n)}
variable {done deps : List (Fm PTm n)} {A B : Fm PTm n}

/-- The empty schedule. -/
def nil : ProofBuild Γ [] where
  derive := by
    intro C hC
    simp at hC

/-- Retrieve any theorem already compiled into the schedule. -/
theorem get (s : ProofBuild Γ done) (hA : A ∈ done) :
    Γ ⊢[PRAAx] A :=
  s.derive A hA

/--
Add a node whose local derivation may use all previously compiled nodes.
`Prf.trans` performs simultaneous cut, replacing each earlier-node hypothesis
by the derivation stored in the build and each base hypothesis by `Prf.hyp`.
-/
def step (s : ProofBuild Γ done)
    (local : done ++ Γ ⊢[PRAAx] A) : ProofBuild Γ (A :: done) where
  derive := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hOld
    · exact local.trans (fun D hD => by
        rcases List.mem_append.mp hD with hDone | hBase
        · exact s.derive D hDone
        · exact Prf.hyp hBase)
    · exact s.derive C hOld

/--
Add a node from an explicit dependency sublist.  The inclusion proof is the
meta-level acyclicity/topological-order certificate.  Unmentioned earlier
nodes are not available to the local proof.
-/
def stepFrom (s : ProofBuild Γ done)
    (hdeps : deps ⊆ done)
    (local : deps ++ Γ ⊢[PRAAx] A) : ProofBuild Γ (A :: done) where
  derive := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hOld
    · exact local.trans (fun D hD => by
        rcases List.mem_append.mp hD with hDep | hBase
        · exact s.derive D (hdeps hDep)
        · exact Prf.hyp hBase)
    · exact s.derive C hOld

/-- A small regression theorem displaying the generated proof-term pattern. -/
theorem compileThree
    {A B C : Fm PTm n}
    (hA : Γ ⊢[PRAAx] A)
    (hB : A :: Γ ⊢[PRAAx] B)
    (hC : B :: A :: Γ ⊢[PRAAx] C) :
    Γ ⊢[PRAAx] C := by
  let s0 : ProofBuild Γ [] := ProofBuild.nil
  let s1 : ProofBuild Γ [A] := ProofBuild.step s0 (by simpa using hA)
  let s2 : ProofBuild Γ [B, A] := ProofBuild.step s1 (by simpa using hB)
  let s3 : ProofBuild Γ [C, B, A] := ProofBuild.step s2 (by simpa using hC)
  exact s3.get (by simp)

end ProofBuild

variable {n : Nat} {Γ : List (Fm PTm n)}

/--
Specialize quantifier-free induction at a finite fuel while retaining an
arbitrary permanent context and one explicit precondition.
-/
theorem invariantAtUnder
    (P : Fm PTm n)
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (fuel : PTm n)
    (base : P :: Γ ⊢[PRAAx] I.subst (inst PTm.zero))
    (step : I :: (P :: Γ).map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0)))) :
    P :: Γ ⊢[PRAAx] I.subst (inst fuel) :=
  Prf.allE fuel (PRA.qfInd I hI base step)

/--
Compile one bounded loop.  The only induction is the allowed QF induction on
`I`; the final extractor may prove a quantified result.
-/
theorem loopUnder
    (P Q : Fm PTm n)
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (fuel : PTm n)
    (base : P :: Γ ⊢[PRAAx] I.subst (inst PTm.zero))
    (step : I :: (P :: Γ).map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0))))
    (finish : I.subst (inst fuel) :: P :: Γ ⊢[PRAAx] Q) :
    P :: Γ ⊢[PRAAx] Q :=
  Prf.impE (Prf.impI finish)
    (invariantAtUnder P I hI fuel base step)

/-- The implication form of `loopUnder`, suitable as a contract-DAG node. -/
theorem loopContract
    (P Q : Fm PTm n)
    (I : Fm PTm (n + 1)) (hI : I.QF)
    (fuel : PTm n)
    (base : P :: Γ ⊢[PRAAx] I.subst (inst PTm.zero))
    (step : I :: (P :: Γ).map Fm.shift ⊢[PRAAx]
      I.subst (repl (PTm.succ (var 0))))
    (finish : I.subst (inst fuel) :: P :: Γ ⊢[PRAAx] Q) :
    Γ ⊢[PRAAx] P ⟶ Q :=
  Prf.impI (loopUnder P Q I hI fuel base step finish)

/-- An explicitly supplied finite witness yields the object existential. -/
theorem existsFromWitness
    (R : Fm PTm (n + 1)) (w : PTm n)
    (hw : Γ ⊢[PRAAx] R.subst (inst w)) :
    Γ ⊢[PRAAx] Fm.ex R :=
  Prf.exI w hw

/--
Two independently produced certificates determine an observable once the
stability comparison is itself an embedded derivation.  No equality or
coherent choice of witnesses is required.
-/
theorem stableObservable
    (C₁ C₂ O : Fm PTm n)
    (h₁ : Γ ⊢[PRAAx] C₁)
    (h₂ : Γ ⊢[PRAAx] C₂)
    (stable : C₁ :: C₂ :: Γ ⊢[PRAAx] O) :
    Γ ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI stable)) h₂) h₁

/--
An external/global theorem is visible as a boundary formula and proof.  This
rule prevents ineffective or nonconstructive information from being smuggled
into a purported primitive-recursive producer.
-/
theorem withBoundary
    (Boundary Goal : Fm PTm n)
    (hBoundary : Γ ⊢[PRAAx] Boundary)
    (body : Boundary :: Γ ⊢[PRAAx] Goal) :
    Γ ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impI body) hBoundary

/-- Exact branch collapse requires both approximation data and a gap witness. -/
theorem exactFromGap
    (Approx Gap Exact : Fm PTm n)
    (hApprox : Γ ⊢[PRAAx] Approx)
    (hGap : Γ ⊢[PRAAx] Gap)
    (sound : Approx :: Gap :: Γ ⊢[PRAAx] Exact) :
    Γ ⊢[PRAAx] Exact :=
  stableObservable Approx Gap Exact hApprox hGap sound

/-- Transport a completed embedded iPRA derivation to the native calculus. -/
def exportNative
    {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) :
    NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

end KernelFiniteUse
end LeanProofs.ConciseIPRA

#print axioms LeanProofs.ConciseIPRA.KernelFiniteUse.ProofBuild.compileThree
#print axioms LeanProofs.ConciseIPRA.KernelFiniteUse.loopContract
#print axioms LeanProofs.ConciseIPRA.KernelFiniteUse.stableObservable
