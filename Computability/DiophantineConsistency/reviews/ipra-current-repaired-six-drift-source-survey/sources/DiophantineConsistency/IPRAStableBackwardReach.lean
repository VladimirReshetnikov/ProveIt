import DiophantineConsistency.IPRAStableBackward
set_option autoImplicit false
namespace DiophantineConsistency.IPRAStableBackwardReach
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRAStableBackward
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- Exactly the formulas reached by the syntax induction from root. -/
inductive Reach (root : Proposition L) : Proposition L → Prop
  | self : Reach root root
  | andLeft {φ ψ} : Reach root (φ ⋏ ψ) → Reach root φ
  | andRight {φ ψ} : Reach root (φ ⋏ ψ) → Reach root ψ
  | orLeft {φ ψ} : Reach root (φ ⋎ ψ) → Reach root φ
  | orRight {φ ψ} : Reach root (φ ⋎ ψ) → Reach root ψ
  | allFree {φ : Semiproposition L 1} : Reach root (∀⁰ φ) → Reach root (free φ)
  | exsFree {φ : Semiproposition L 1} : Reach root (∃⁰ φ) → Reach root (free φ)

omit [L.DecidableEq] in
theorem reachSupport (root : Proposition L) : Support (Reach root) where
  and_left := Reach.andLeft
  and_right := Reach.andRight
  or_left := Reach.orLeft
  or_right := Reach.orRight
  all_free := Reach.allFree
  exs_free := Reach.exsFree

noncomputable def nativeBackwardReach (φ : Proposition L)
    (stable : ∀ ψ, Reach φ ψ → NeedsStability ψ → Λ ⊢! ∼∼native ψ 🡒 native ψ) :
    Λ ⊢! φᴺ 🡒 native φ :=
  nativeBackward (Reach φ) (reachSupport φ) stable φ Reach.self
end DiophantineConsistency.IPRAStableBackwardReach
