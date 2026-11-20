import IPRADerivations.Core.Semiring

/-!
Packet: `foundations/ipra_transport_framework_2026-11-20`. Imported from the packet's `lean/ObjectRewrite.lean`:
`compile` (a metatheory derivation in a word-rewriting system whose relations hold as object equations yields an
object equation of the words), `word_append`, `congrWord`, `swapTranslations`, `closedSquare`.

 Exact specialization in ordinary iPRA. Every conclusion below is an
embedded derivation; word syntax and its proof are fixed in the metatheory. -/
namespace LeanProofs.IPRA.Foundations.Transport.ObjectRewrite
open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open scoped Fm

variable {E R : Type} {n : Nat} {Γ : List (Fm PTm n)}

def word (f : E → PTm n → PTm n) : List E → PTm n → PTm n
  | [], x => x
  | e :: w, x => word f w (f e x)

theorem word_append (f : E → PTm n → PTm n) (u v : List E) (x : PTm n) :
    word f (u ++ v) x = word f v (word f u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (f e x)

inductive Derivation (lhs rhs : R → List E) : List E → List E → Prop where
  | refl (u) : Derivation lhs rhs u u
  | cell (p s) (r : R) : Derivation lhs rhs (p ++ lhs r ++ s) (p ++ rhs r ++ s)
  | symm {u v} : Derivation lhs rhs u v → Derivation lhs rhs v u
  | trans {u v w} : Derivation lhs rhs u v → Derivation lhs rhs v w → Derivation lhs rhs u w

theorem congrWord (f : E → PTm n → PTm n)
    (hcong : ∀ e {a b}, (Γ ⊢[PRAAx] a ≐ b) → (Γ ⊢[PRAAx] f e a ≐ f e b))
    (w : List E) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] word f w x ≐ word f w y := by
  induction w generalizing x y with
  | nil => exact h
  | cons e w ih => exact ih (hcong e h)

theorem compile (f : E → PTm n → PTm n)
    (hcong : ∀ e {a b}, (Γ ⊢[PRAAx] a ≐ b) → (Γ ⊢[PRAAx] f e a ≐ f e b))
    {lhs rhs : R → List E}
    (law : ∀ r t, Γ ⊢[PRAAx] word f (lhs r) t ≐ word f (rhs r) t)
    {u v} (proof : Derivation lhs rhs u v) (x : PTm n) :
    Γ ⊢[PRAAx] word f u x ≐ word f v x := by
  induction proof with
  | refl w => exact .eqRefl _
  | cell p s r => simpa only [word_append] using congrWord f hcong s (law r (word f p x))
  | symm _ ih => exact Prf.eqSymm ih
  | trans _ _ ih₁ ih₂ => exact Prf.eqTrans ih₁ ih₂

/-- Swapping two translations under arbitrary identical prefixes and suffixes. -/
theorem swapTranslations (d : E → PTm n) (a b : E) (p s : List E) (x : PTm n) :
    Γ ⊢[PRAAx]
      word (fun e t => t + d e) (p ++ [a,b] ++ s) x ≐
      word (fun e t => t + d e) (p ++ [b,a] ++ s) x := by
  let f : E → PTm n → PTm n := fun e t => t + d e
  let lhs : Unit → List E := fun _ => [a,b]
  let rhs : Unit → List E := fun _ => [b,a]
  apply compile (Γ := Γ) f (lhs := lhs) (rhs := rhs) _ _ (.cell p s ()) x
  · intro e u v h
    exact congrAdd h (.eqRefl (d e))
  · intro _ t
    exact add_right_comm t (d a) (d b)

/-- A closed sentence exhibiting the square relation with a nonempty suffix. -/
theorem closedSquare :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all (Fm.all (Fm.all
      ((((Syn.var 0 : PTm 3) + Syn.var 1) + Syn.var 2) + Syn.var 1 ≐
       ((Syn.var 0 + Syn.var 2) + Syn.var 1) + Syn.var 1))) := by
  apply Prf.allI
  apply Prf.allI
  apply Prf.allI
  let d : Bool → PTm 3 := fun e => if e then Syn.var 2 else Syn.var 1
  exact swapTranslations d false true [] [false] (Syn.var 0)

end LeanProofs.IPRA.Foundations.Transport.ObjectRewrite
