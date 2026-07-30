/-! # Girard's paradox, Hurkens-style, in Lean 4

Hurkens' simplification of Girard's paradox, carried out in Lean 4 against a
hypothetical impredicative closure of `Type u` over itself.  The four
hypotheses `pi`, `lam`, `app`, `beta` say exactly that `Type u` contains a
code for every product of a `Type u`-indexed family of types — the single
ingredient of `Type : Type` that Lean's predicative hierarchy denies.  Lean's
own impredicative `Prop` plays the role of System U⁻'s inner sort `∗`; the
hypotheses play the role of the outer impredicative sort `□`.  From the four
ingredients we derive `False`, with no axioms at all.

Everything else in Hurkens' argument already lives in Lean, because Lean's
impredicative `Prop` supplies System U⁻'s sort `∗`: the powerset `Pw X` stays
in `Type u`, and so does the operator `F X := (Pw (Pw X) → X) → Pw (Pw X)`.
Exactly one judgment fails.  The product `(X : Type u) → F X` lands in
`Type (u+1)`, never in `Type u`: the domain `Type u` is itself a term of
`Sort (u+2)`, so the product has level `imax (u+2) (u+1) = u+2`.  Hurkens'
universe needs that product back at `Type u`, because `σ` instantiates an
element of it at the universe itself.  The hypotheses below grant precisely
that one flattening, and `no_internal_universe` shows the same collapse in
Tarski style: a decoding `El : V → Type u` with a section is equally fatal.

Girard, *Interprétation fonctionnelle et élimination des coupures*, Thèse
d'État, 1972 (the original paradox in System U).  Coquand, *An Analysis of
Girard's Paradox*, LICS 1986.  Hurkens, *A Simplification of Girard's
Paradox*, TLCA 1995, LNCS 902 — the derivation followed here.  Two prior
formalizations were consulted for the mathematics only, not for code: the
Coq standard library's `Logic/Hurkens.v` and mathlib's
`Counterexamples/Girard.lean`.  The proof below, its lemma decomposition,
and its naming are independent.
-/

set_option autoImplicit false

namespace LeanProofs.HurkensParadox

universe u

/-- The powerset of `X : Type u` stays in `Type u` because `Prop` is
impredicative: `X → Prop : Sort (imax (u+1) 1) = Type u`. -/
def Pw (X : Type u) : Type u := X → Prop

/-- **Girard's paradox** (Hurkens' simplification). -/
theorem girard
    (pi : (Type u → Type u) → Type u)
    (lam : ∀ {F : Type u → Type u}, (∀ X, F X) → pi F)
    (app : ∀ {F : Type u → Type u}, pi F → ∀ X, F X)
    (beta : ∀ {F : Type u → Type u} (f : ∀ X, F X) (X), app (lam f) X = f X) :
    False :=
  let F : Type u → Type u := fun X => (Pw (Pw X) → X) → Pw (Pw X)
  let U : Type u := pi F
  let τ : Pw (Pw U) → U := fun t =>
    lam (F := F) (fun X f p => t (fun x => p (f (app x X f))))
  let σ : U → Pw (Pw U) := fun s => app s U τ
  have sigma_tau : ∀ (t : Pw (Pw U)) (p : Pw U),
      σ (τ t) p = t (fun x => p (τ (σ x))) := fun t p =>
    congrFun
      (congrFun (beta (F := F) (fun X f p => t (fun x => p (f (app x X f)))) U) τ)
      p
  let ω : Pw (Pw U) := fun p => ∀ x, σ x p → p x
  let Ω : U := τ ω
  have lemA : ∀ p : Pw U, (∀ x, σ x p → p x) → p Ω := fun p H =>
    H Ω (Eq.mpr (sigma_tau ω p)
      (fun x hx => H (τ (σ x)) (Eq.mpr (sigma_tau (σ x) p) hx)))
  let Δ : Pw U := fun y => ¬ (∀ p, σ y p → p (τ (σ y)))
  have p1 : ∀ x, σ x Δ → Δ x := fun x h2 h3 =>
    h3 Δ h2 (fun p h4 =>
      h3 (fun y => p (τ (σ y))) (Eq.mp (sigma_tau (σ x) p) h4))
  lemA Δ p1 (fun p h5 =>
    lemA (fun y => p (τ (σ y))) (Eq.mp (sigma_tau ω p) h5))

/-- info: 'LeanProofs.HurkensParadox.girard' does not depend on any axioms -/
#guard_msgs in #print axioms girard

/-- Transporting a dependent application along an equality of indices. -/
theorem cast_apply {F : Type u → Type u} (g : ∀ Z, F Z) {A B : Type u}
    (e : A = B) : e ▸ g A = g B := by cases e; rfl

/-- **No internal universe**: no `V : Type u` admits a decoding
`El : V → Type u` with a section `code : Type u → V` (`El ∘ code = id`).
Such a `V` would let products over `Type u` be re-indexed as products over
`V` itself, producing Girard's four ingredients. -/
theorem no_internal_universe
    (V : Type u) (El : V → Type u) (code : Type u → V)
    (h : ∀ X, El (code X) = X) : False :=
  girard
    (pi := fun F => (v : V) → F (El v))
    (lam := fun g v => g (El v))
    (app := fun f X => h X ▸ f (code X))
    (beta := fun g X => cast_apply g (h X))

/-- info: 'LeanProofs.HurkensParadox.no_internal_universe' does not depend on any axioms -/
#guard_msgs in #print axioms no_internal_universe

end LeanProofs.HurkensParadox
