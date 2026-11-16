import ObjectDemand

/-!
# Exact remaining object-theory targets

Every declaration here is a DEFINITION OF A PROPOSITION, not a theorem or an
axiom.  These are the remaining steps for a complete `Prf PRAAx` implementation
of the two-pass compiler.  The companion README gives the proof order.
-/

namespace LeanProofs.ConciseIPRA.DemandCompiler

open Syn
open scoped Fm

def horizonTerm {n : Nat} (D : PR 2) (N k t : PTm n) : PTm n :=
  PTm.app (horizonSymbol D) (v3 N k t)

def forwardTerm {n : Nat} (D : PR 2) (b : PR 1) (F : PR 3)
    (t N k : PTm n) : PTm n := PTm.app (forwardSymbol D b F) (v3 t N k)

def compiledTerm {n : Nat} (D : PR 2) (b : PR 1) (F : PR 3)
    (N k : PTm n) : PTm n := PTm.app (compiled D b F) (v2 N k)

def dTerm {n : Nat} (D : PR 2) (N k : PTm n) : PTm n := PTm.app D (v2 N k)
def bTerm {n : Nat} (b : PR 1) (k : PTm n) : PTm n := PTm.app b (fun _ => k)
def fTerm {n : Nat} (F : PR 3) (N k s : PTm n) : PTm n := PTm.app F (v3 N k s)

/-- Needed arithmetic identity; natural subtraction is represented by monusRev. -/
def MonusSelfTarget : Prop := ∀ {n : Nat} (Γ : List (Fm PTm n)) (N : PTm n),
  Γ ⊢[PRAAx] subTerm N N ≐ PTm.zero

/-- The key exact finite coherence identity, with no order side condition. -/
def BackwardCoherenceTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (j N k : PTm n),
    Γ ⊢[PRAAx] backwardTerm D (PTm.succ j) (PTm.succ N) k ≐
      backwardTerm D j N (dTerm D N k)

def HorizonFinalTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (N k : PTm n),
    Γ ⊢[PRAAx] horizonTerm D N k N ≐ k

def ForwardBaseTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (b : PR 1) (F : PR 3)
      (N k : PTm n),
    Γ ⊢[PRAAx] forwardTerm D b F PTm.zero N k ≐
      bTerm b (horizonTerm D N k PTm.zero)

def ForwardStepTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (b : PR 1) (F : PR 3)
      (t N k : PTm n),
    Γ ⊢[PRAAx] forwardTerm D b F (PTm.succ t) N k ≐
      fTerm F t (horizonTerm D N k (PTm.succ t)) (forwardTerm D b F t N k)

def CompiledZeroTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (b : PR 1) (F : PR 3)
      (k : PTm n),
    Γ ⊢[PRAAx] compiledTerm D b F PTm.zero k ≐ bTerm b k

def CompiledSuccessorTarget : Prop :=
  ∀ {n : Nat} (Γ : List (Fm PTm n)) (D : PR 2) (b : PR 1) (F : PR 3)
      (N k : PTm n),
    Γ ⊢[PRAAx] compiledTerm D b F (PTm.succ N) k ≐
      fTerm F N k (compiledTerm D b F N (dTerm D N k))

end LeanProofs.ConciseIPRA.DemandCompiler
