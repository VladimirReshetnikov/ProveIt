import IPRADerivations.Core.Basic

/-!
# Proof-Carrying Finitary Modules: structural core

This is a source-oriented candidate against ProveIt commit
`7fa3ba48e8f62e8018ed954faaa48b908217eaf1`.

The record deliberately stores an actual object-theory derivation.  The file
has not been compiled in the artifact environment because Lean is unavailable
there.  No theorem below is claimed checked by this archive.
-/

namespace LeanProofs.IPRA.Framework

open LeanProofs.ConciseIPRA
open scoped Fm

/-- A finite interface whose payload is already a derivation in ordinary iPRA. -/
structure Module (n : ℕ) where
  req : List (Fm PTm n)
  out : Fm PTm n
  proof : req ⊢[PRAAx] out

namespace Module

variable {n m : ℕ}

/-- Simultaneous specialization of every free variable. -/
def specialize (M : Module n) (σ : Fin n → PTm m) : Module m where
  req := M.req.map (fun φ => φ.subst σ)
  out := M.out.subst σ
  proof := M.proof.subst σ

/-- Use a module after deriving every requirement from a common context. -/
def discharge (M : Module n) {Δ : List (Fm PTm n)}
    (h : ∀ φ ∈ M.req, Δ ⊢[PRAAx] φ) :
    Δ ⊢[PRAAx] M.out :=
  M.proof.trans h

/-- Structural weakening of a module proof. -/
def useUnder (M : Module n) {Δ : List (Fm PTm n)}
    (h : M.req ⊆ Δ) :
    Δ ⊢[PRAAx] M.out :=
  M.proof.weaken h

/-- Package an already closed object derivation. -/
def closed {φ : Fm PTm n}
    (h : ([] : List (Fm PTm n)) ⊢[PRAAx] φ) :
    Module n where
  req := []
  out := φ
  proof := h

/-- Package the hypothesis rule as a one-requirement module. -/
def assumption (φ : Fm PTm n) : Module n where
  req := [φ]
  out := φ
  proof := Prf.hyp0

end Module

/-- A one-input contract. -/
abbrev Contract {n : ℕ} (A B : Fm PTm n) := [A] ⊢[PRAAx] B

namespace Contract

variable {n : ℕ} {A B C : Fm PTm n}

/-- Identity contract. -/
def id (A : Fm PTm n) : Contract A A := Prf.hyp0

/-- Sequential composition is simultaneous cut with one requirement. -/
def comp (f : Contract A B) (g : Contract B C) : Contract A C := by
  apply g.trans
  intro φ hφ
  simp only [List.mem_singleton] at hφ
  subst φ
  exact f

end Contract

end LeanProofs.IPRA.Framework
