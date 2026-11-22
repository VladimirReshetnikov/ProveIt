import ConciseIPRA.PR
import Merge

/- Object-theory cut along a supplied, externally finite graph. The arity n,
context Γ, and object terms may be arbitrary. The graph/list is a Lean
parameter, *not* an internal numerical graph variable. -/
namespace EffectiveFinality
open LeanProofs.ConciseIPRA
open scoped Fm
variable {V : Type} {n : ℕ} (Γ : List (Fm PTm n))

/-- Compile a path to a sequent for any relation with derivable equivalence laws. -/
theorem pathDerivation (R : V → V → Prop) (A : V → V → Fm PTm n)
    (reflA : ∀ x, Γ ⊢[PRAAx] A x x)
    (symA : ∀ x y, (Γ ⊢[PRAAx] A x y) → (Γ ⊢[PRAAx] A y x))
    (transA : ∀ x y z, (Γ ⊢[PRAAx] A x y) → (Γ ⊢[PRAAx] A y z) → (Γ ⊢[PRAAx] A x z))
    (edgeA : ∀ x y, R x y → (Γ ⊢[PRAAx] A x y)) {x y} (w : Walk R x y) :
    Γ ⊢[PRAAx] A x y := by
  induction w with
  | trivial x => exact reflA x
  | edge e => exact edgeA _ _ e
  | reverse _ ih => exact symA _ _ ih
  | join _ _ ih₁ ih₂ => exact transA _ _ _ ih₁ ih₂

/-- Merge-label equality is an external decision; the conclusion is an
actual iPRA sequent. Thus label comparison can guide equational cut. -/
theorem classCut [DecidableEq V] (es : List (V × V)) (t : V → PTm n)
    (hedge : ∀ x y, Adj es x y → (Γ ⊢[PRAAx] t x ≐ t y)) {x y}
    (h : label es x = label es y) : Γ ⊢[PRAAx] t x ≐ t y :=
  pathDerivation Γ (Adj es) (fun a b => t a ≐ t b) (fun a => .eqRefl (t a))
    (fun _ _ e => e.eqSymm) (fun _ _ _ e f => e.eqTrans f) hedge
    ((same_label_iff es x y).1 h)

/-- A concrete chain with a reversed input edge. -/
theorem sampleCut (t : Nat → PTm n)
    (h₁ : Γ ⊢[PRAAx] t 1 ≐ t 0) (h₂ : Γ ⊢[PRAAx] t 1 ≐ t 2) :
    Γ ⊢[PRAAx] t 0 ≐ t 2 := by
  apply classCut Γ [(1, 2), (1, 0)] t _ (by decide)
  intro x y h
  simp [Adj] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h₂
  · exact h₁

end EffectiveFinality
