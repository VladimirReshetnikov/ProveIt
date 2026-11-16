import ConciseIPRA.PR

/-!
# Categorical equation proofs in the actual object calculus

This file targets ProveIt commit
bb86091690bc4f920f046a37cfc87719299b4019.

Every theorem below concludes `Prf PRAAx ...`; none merely proves an
equation between host Lean naturals. The category laws are supplied as
object derivations, so these lemmas do not assert that an arbitrary
primitive recursive binary operation is a category composition.

Formalization status: source written against the inspected upstream API.
This file has NOT been compiled in this environment. It contains no `sorry`
or new axiom. Compilation, and supplying the law derivations for concrete
presentations, remain separate obligations.
-/

namespace LeanProofs.ConciseIPRA.CategoryObject

open Syn
open scoped Fm

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- A two-element tuple without relying on vector notation. -/
def args₂ (a b : PTm n) : Fin 2 → PTm n :=
  Fin.cases a (Fin.cases b Fin.elim0)

/-- Application of a fixed binary PR symbol. -/
def bin (op : PR 2) (a b : PTm n) : PTm n := PTm.app op (args₂ a b)

/-- Object-theory congruence for a fixed binary PR symbol. -/
theorem bin_congr (op : PR 2) {a a' b b' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] bin op a b ≐ bin op a' b' := by
  have hs : ∀ i : Fin 2,
      Γ ⊢[PRAAx] args₂ a b i ≐ args₂ a' b' i :=
    Fin.cases ha (Fin.cases hb Fin.elim0)
  simpa only [PTm.subst_app, Syn.subst_var] using
    (Prf.eqCongr (PTm.app op Syn.var : PTm 2)
      (σ := args₂ a b) (σ' := args₂ a' b') hs)

/-- A left inverse and a right inverse of the same arrow coincide.

`bin comp g f` means `g ∘ f`. The typed category guards must be
included in Γ when obtaining the five local law derivations.
-/
theorem inverse_unique (comp : PR 2) (idA idB f g h : PTm n)
    (rightUnit : Γ ⊢[PRAAx] bin comp g idB ≐ g)
    (rightInverse : Γ ⊢[PRAAx] bin comp f h ≐ idB)
    (assoc : Γ ⊢[PRAAx]
      bin comp g (bin comp f h) ≐ bin comp (bin comp g f) h)
    (leftInverse : Γ ⊢[PRAAx] bin comp g f ≐ idA)
    (leftUnit : Γ ⊢[PRAAx] bin comp idA h ≐ h) :
    Γ ⊢[PRAAx] g ≐ h := by
  exact Prf.eqTrans (Prf.eqSymm rightUnit)
    (Prf.eqTrans (bin_congr comp (Prf.eqRefl g) (Prf.eqSymm rightInverse))
      (Prf.eqTrans assoc
        (Prf.eqTrans (bin_congr comp leftInverse (Prf.eqRefl h)) leftUnit)))

/-- The finite conjunction of the five observations consumed by the proof. -/
def inversePremises (comp : PR 2) (idA idB f g h : PTm n) : Fm PTm n :=
  (bin comp g idB ≐ g) ⋏
  (bin comp f h ≐ idB) ⋏
  (bin comp g (bin comp f h) ≐ bin comp (bin comp g f) h) ⋏
  (bin comp g f ≐ idA) ⋏
  (bin comp idA h ≐ h)

/-- An assumption-free object derivation of the corresponding implication.

There are no extra arithmetic or categorical axioms in its theory.
The categorical laws appear in the antecedent of the proved formula.
The `n` free variables remain schematic; universal closure is a separate
sequence of `Prf.allI` applications.
-/
theorem inverse_unique_imp (comp : PR 2) (idA idB f g h : PTm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      inversePremises comp idA idB f g h ⟶ (g ≐ h) := by
  apply Prf.impI
  have hp : [inversePremises comp idA idB f g h] ⊢[PRAAx]
      inversePremises comp idA idB f g h := Prf.hyp0
  exact inverse_unique comp idA idB f g h
    (Prf.andE₁ hp)
    (Prf.andE₁ (Prf.andE₂ hp))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hp)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hp))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hp))))

/-- The determining calculation in covariant Yoneda.

`alpha B u` is the component of a supplied transformation;
`act f x` is the action of the supplied functor.
Naturality is used only at `idA`, followed by the right-unit law.
This is the computation needed to show that every transformation is
determined by its value on the identity; construction of the inverse
transformation and its naturality are separate categorical lemmas.
-/
theorem yoneda_covariant_component (comp alpha act : PR 2) (A B idA f : PTm n)
    (naturalityAtId : Γ ⊢[PRAAx]
      bin act f (bin alpha A idA) ≐ bin alpha B (bin comp f idA))
    (rightUnit : Γ ⊢[PRAAx] bin comp f idA ≐ f) :
    Γ ⊢[PRAAx] bin alpha B f ≐ bin act f (bin alpha A idA) := by
  exact Prf.eqSymm (Prf.eqTrans naturalityAtId
    (bin_congr alpha (Prf.eqRefl B) rightUnit))

/-- The contravariant version used for the representable presheaf
`Hom(-, A)`. Here `f : X → A`, and `act f` maps elements of `F(A)`
to elements of `F(X)`. -/
theorem yoneda_component (comp alpha act : PR 2) (A X idA f : PTm n)
    (naturalityAtId : Γ ⊢[PRAAx]
      bin act f (bin alpha A idA) ≐ bin alpha X (bin comp idA f))
    (leftUnit : Γ ⊢[PRAAx] bin comp idA f ≐ f) :
    Γ ⊢[PRAAx] bin alpha X f ≐ bin act f (bin alpha A idA) := by
  exact Prf.eqSymm (Prf.eqTrans naturalityAtId
    (bin_congr alpha (Prf.eqRefl X) leftUnit))

/-- This purely logical constructor is the object proof used in composing
proof-carrying contracts after the explicit substitutions are performed. -/
theorem contract_cut {A B C : Fm PTm n}
    (first : Γ ⊢[PRAAx] A ⟶ B)
    (second : Γ ⊢[PRAAx] B ⟶ C) :
    Γ ⊢[PRAAx] A ⟶ C := Prf.impTrans first second

/-!
Setoid caveat. `≐` is equality of arithmetic codes. For a presentation whose
categorical equality is a nontrivial setoid relation, replace each equality
in these statements by its arithmetic relation formula, and provide
object-level symmetry, transitivity, and binary congruence for that relation.
The same five-step derivation then works; arithmetic Leibniz substitution
alone does not establish setoid congruence.
-/

end LeanProofs.ConciseIPRA.CategoryObject

-- These audit commands will run only when a future Lean compilation succeeds.
#print axioms LeanProofs.ConciseIPRA.CategoryObject.inverse_unique_imp
#print axioms LeanProofs.ConciseIPRA.CategoryObject.yoneda_component
#print axioms LeanProofs.ConciseIPRA.CategoryObject.contract_cut
