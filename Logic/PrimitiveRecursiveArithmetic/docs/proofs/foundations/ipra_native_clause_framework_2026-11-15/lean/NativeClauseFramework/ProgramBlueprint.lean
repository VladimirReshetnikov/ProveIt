import NativeClauseFramework.Bridge

/-!
# Dependent finite proof programs -- blueprint

This module gives the intended types for the first generic compiler milestone.
It is deliberately explicit about the remaining proof holes.  The module was
not compiled in the artifact runtime.
-/

namespace LeanProofs.IPRA.NativeClauseFramework

open LeanProofs.ConciseIPRA

/-- One node may assume all previously available outputs.  A sparse-dependency
variant can store indices and map them to a shorter assumption list. -/
structure Node (n : ℕ) (Γ : List (Cl n)) (available : List (NFm n)) where
  out : NFm n
  local : KPrf (available.map Cl.asm ++ Γ) out

/-- A topologically ordered program, newest output first. -/
inductive Program (n : ℕ) (Γ : List (Cl n)) : List (NFm n) → Type
  | nil : Program n Γ []
  | snoc {outs : List (NFm n)} (p : Program n Γ outs)
      (node : Node n Γ outs) : Program n Γ (node.out :: outs)

/-- Every listed output has been compiled from the base context. -/
def Compiled {n : ℕ} (Γ : List (Cl n)) (outs : List (NFm n)) : Prop :=
  ∀ A, A ∈ outs → KPrf Γ A

/-- Main graph-fold theorem.  Induct on `Program`; the step is `cutAsmList`. -/
theorem Program.compile {n : ℕ} {Γ : List (Cl n)} {outs : List (NFm n)}
    (p : Program n Γ outs) : Compiled Γ outs := by
  sorry

/-- Extract the newest output of a nonempty compiled program. -/
theorem Program.compileHead {n : ℕ} {Γ : List (Cl n)} {outs : List (NFm n)}
    (p : Program n Γ outs) {A : NFm n} (hA : A ∈ outs) : KPrf Γ A := by
  exact p.compile A hA

/-- Specialize a node family by checked native substitution. -/
def Node.subst {n m : ℕ} {Γ : List (Cl n)} {available : List (NFm n)}
    (node : Node n Γ available) (σ : Fin n → Tm m) :
    Node m (Γ.map fun c => c.subst σ) (available.map fun A => A.subst σ) := by
  sorry

end LeanProofs.IPRA.NativeClauseFramework
