import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Staged specialization and proof composition for iPRA

This module is intended to live in the ProveIt root Lake workspace.  Its
trusted endpoint is always `Prf PRAAx`; it never turns an ambient Lean theorem
into an object-theory theorem.

The new ingredient relative to the existing fixed-context `ProofBuild`
experiments is *arity-normalized staged specialization*.  A local theorem may
live in any finite parameter frame.  It is first specialized by `Prf.subst`,
then weakened into the current global frame, and only then composed by
`Prf.trans`.  Hence substitutions, contexts, and binders are handled once in a
small reusable kernel rather than separately in every application packet.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA
namespace StagedContractKernel

open Syn
open scoped Fm

/-- Specialize a local object-theory derivation and align its context. -/
theorem instantiateInto
    {k n : Nat}
    {Delta : List (Fm PTm k)} {A : Fm PTm k}
    (local : Delta ⊢[PRAAx] A)
    (sigma : Fin k -> PTm n)
    {Theta : List (Fm PTm n)}
    (available : Delta.map (fun B => B.subst sigma) ⊆ Theta) :
    Theta ⊢[PRAAx] A.subst sigma :=
  (local.subst sigma).weaken available

/-- Every theorem in `done` has already been compiled from the permanent base
context `Gamma`.  The order is reverse topological: the newest theorem is at
the head. -/
structure ProofBuild {n : Nat}
    (Gamma : List (Fm PTm n)) (done : List (Fm PTm n)) where
  derive : forall A, A ∈ done -> Gamma ⊢[PRAAx] A

namespace ProofBuild

variable {n : Nat} {Gamma : List (Fm PTm n)}
variable {done deps : List (Fm PTm n)} {A : Fm PTm n}

/-- Empty proof schedule. -/
def nil : ProofBuild Gamma [] where
  derive := by
    intro B hB
    simp at hB

/-- Retrieve a compiled theorem. -/
theorem get (s : ProofBuild Gamma done) (hA : A ∈ done) :
    Gamma ⊢[PRAAx] A :=
  s.derive A hA

/-- Add a theorem whose local proof may use every already compiled theorem. -/
def step (s : ProofBuild Gamma done)
    (local : done ++ Gamma ⊢[PRAAx] A) :
    ProofBuild Gamma (A :: done) where
  derive := by
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hOld
    · exact local.trans (fun C hC => by
        rcases List.mem_append.mp hC with hDone | hBase
        · exact s.derive C hDone
        · exact Prf.hyp hBase)
    · exact s.derive B hOld

/-- Add a theorem using an explicit dependency sublist. -/
def stepFrom (s : ProofBuild Gamma done)
    (hdeps : deps ⊆ done)
    (local : deps ++ Gamma ⊢[PRAAx] A) :
    ProofBuild Gamma (A :: done) where
  derive := by
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hOld
    · exact local.trans (fun C hC => by
        rcases List.mem_append.mp hC with hDep | hBase
        · exact s.derive C (hdeps hDep)
        · exact Prf.hyp hBase)
    · exact s.derive B hOld

end ProofBuild

/-- One local theorem after all domain-specific syntax has been fixed, but
before its local parameter frame has been instantiated into the global one. -/
structure NodeObligation {n : Nat}
    (Gamma done : List (Fm PTm n)) where
  arity : Nat
  localContext : List (Fm PTm arity)
  localGoal : Fm PTm arity
  args : Fin arity -> PTm n
  localProof : localContext ⊢[PRAAx] localGoal
  available : localContext.map (fun B => B.subst args) ⊆ done ++ Gamma

namespace NodeObligation

variable {n : Nat} {Gamma done : List (Fm PTm n)}

/-- The specialized goal contributed by a node. -/
def goal (N : NodeObligation Gamma done) : Fm PTm n :=
  N.localGoal.subst N.args

/-- Compile one arity-normalized node.  The implementation is exactly:
substitution, context alignment, then simultaneous cut. -/
def compile
    (s : ProofBuild Gamma done)
    (N : NodeObligation Gamma done) :
    ProofBuild Gamma (N.goal :: done) :=
  s.step (instantiateInto N.localProof N.args N.available)

end NodeObligation

/-- Specialize a closed theorem at arbitrary terms. -/
theorem specializeClosed
    {k n : Nat} {A : Fm PTm k}
    (h : ([] : List (Fm PTm k)) ⊢[PRAAx] A)
    (sigma : Fin k -> PTm n)
    {Gamma : List (Fm PTm n)} :
    Gamma ⊢[PRAAx] A.subst sigma := by
  exact (h.subst sigma).weaken (List.nil_subset _)

/-- All object-theory obligations for one bounded primitive-recursive loop. -/
structure LoopObligation {n : Nat}
    (Gamma : List (Fm PTm n)) (P Q : Fm PTm n) where
  invariant : Fm PTm (n + 1)
  invariantQF : invariant.QF
  fuel : PTm n
  base : P :: Gamma ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: (P :: Gamma).map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (var 0)))
  finish : invariant.subst (inst fuel) :: P :: Gamma ⊢[PRAAx] Q

namespace LoopObligation

variable {n : Nat} {Gamma : List (Fm PTm n)} {P Q : Fm PTm n}

/-- Quantifier-free induction compiles a loop to an implication contract. -/
theorem compile (L : LoopObligation Gamma P Q) :
    Gamma ⊢[PRAAx] P ⟶ Q := by
  apply Prf.impI
  have hAll : P :: Gamma ⊢[PRAAx] Fm.all L.invariant :=
    PRA.qfInd L.invariant L.invariantQF L.base L.step
  have hFuel : P :: Gamma ⊢[PRAAx] L.invariant.subst (inst L.fuel) :=
    Prf.allE L.fuel hAll
  exact L.finish.trans (fun B hB => by
    rcases List.mem_cons.mp hB with rfl | hTail
    · exact hFuel
    · exact Prf.hyp hTail)

end LoopObligation

/-- Introduce a supplied finite witness without any choice principle. -/
theorem existsFromWitness
    {n : Nat} {Gamma : List (Fm PTm n)}
    (R : Fm PTm (n + 1)) (w : PTm n)
    (hw : Gamma ⊢[PRAAx] R.subst (inst w)) :
    Gamma ⊢[PRAAx] Fm.ex R :=
  Prf.exI w hw

/-- Erase an internal relational choice once branch-independence has itself
been proved in the object theory. -/
theorem stableObservable
    {n : Nat} {Gamma : List (Fm PTm n)}
    (C1 C2 O : Fm PTm n)
    (h1 : Gamma ⊢[PRAAx] C1)
    (h2 : Gamma ⊢[PRAAx] C2)
    (stable : C1 :: C2 :: Gamma ⊢[PRAAx] O) :
    Gamma ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI stable)) h2) h1

/-- Make a nonuniform or externally supplied mathematical input an explicit
boundary theorem rather than disguising it as a primitive-recursive producer. -/
theorem withBoundary
    {n : Nat} {Gamma : List (Fm PTm n)}
    (Boundary Goal : Fm PTm n)
    (hBoundary : Gamma ⊢[PRAAx] Boundary)
    (body : Boundary :: Gamma ⊢[PRAAx] Goal) :
    Gamma ⊢[PRAAx] Goal :=
  Prf.impE (Prf.impI body) hBoundary

/-- Exact branch collapse from approximation plus an explicit gap theorem. -/
theorem exactFromGap
    {n : Nat} {Gamma : List (Fm PTm n)}
    (Approx Gap Exact : Fm PTm n)
    (hApprox : Gamma ⊢[PRAAx] Approx)
    (hGap : Gamma ⊢[PRAAx] Gap)
    (erase : Approx :: Gap :: Gamma ⊢[PRAAx] Exact) :
    Gamma ⊢[PRAAx] Exact :=
  stableObservable Approx Gap Exact hApprox hGap erase

/-- Export only after the ordinary iPRA derivation is complete. -/
def exportNative
    {n : Nat} {Gamma : List (Fm PTm n)} {A : Fm PTm n}
    (h : Gamma ⊢[PRAAx] A) :
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA A) :=
  pra_iff_native.mp h

end StagedContractKernel
end LeanProofs.ConciseIPRA

#print axioms LeanProofs.ConciseIPRA.StagedContractKernel.instantiateInto
#print axioms LeanProofs.ConciseIPRA.StagedContractKernel.NodeObligation.compile
#print axioms LeanProofs.ConciseIPRA.StagedContractKernel.LoopObligation.compile
