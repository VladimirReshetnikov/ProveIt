import CategoryIPRA.LocalYoneda

/-!
# Representability consequences inside the iPRA object language

This file is an integration draft against ProveIt commit
72d37f6d06fa7b5bd0a46732060446d1cffa3f2d, Lean 4.32.0.
It was not compiled in the generation environment: no Lean executable was
available. There are no `sorry`, `admit`, or newly declared axioms.

The conclusions below are derivations `Γ ⊢[PRAAx] φ`, rather than only
ambient mathematical statements about an interpretation of arithmetic.
Category data are `PTm` and `Fm` syntax, not arbitrary function fields.

The imported source already proves the presentation-wise Yoneda identity.
The additions show (1) faithfulness by evaluation at the identity, and
(2) how specified mutually inverse transformations between representables
produce both inverse equations for their inducing arrows. All formula and
term substitution is inherited from the existing object-language library.
-/

namespace CategoryIPRA.Representability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Yoneda
open CategoryIPRA.LocalYoneda
open Syn
open scoped Fm

variable {C : Pres} (L : C.Laws)
variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Agreement of two represented families at the identity implies equality
of their inducing arrows. The complete pointwise equality hypothesis is
stronger than the single displayed instance, so it is not needed here. -/
theorem represented_faithful {A B u v : PTm n}
    (hu : Γ ⊢[PRAAx] C.hom A B u)
    (hv : Γ ⊢[PRAAx] C.hom A B v)
    (h : Γ ⊢[PRAAx] C.eqv A B
      (C.comp A A B u (C.id1 A))
      (C.comp A A B v (C.id1 A))) :
    Γ ⊢[PRAAx] C.eqv A B u v := by
  exact L.eqv_trans (L.eqv_symm (L.id_right hu))
    (L.eqv_trans h (L.id_right hv))

/-- An arrow induced by a specified transformation between representables. -/
def inducing (α : PTm 4) (A B : PTm n) : PTm n :=
  al α B A A (C.id1 A)

/-- The first round-trip component of a specified natural isomorphism
implies `v ∘ u = 1_A`. Here `α : h_A → h_B` and `β : h_B → h_A` are
specified by terms. Only the naturality of `β` is used in this equation. -/
theorem representable_inverse_left {α β : PTm 4}
    {A B : PTm n}
    (NA : AtLaws C (rep C) α Γ B A)
    (NB : AtLaws C (rep C) β Γ A B)
    (hA : Γ ⊢[PRAAx] C.obj A)
    (hB : Γ ⊢[PRAAx] C.obj B)
    (hround : Γ ⊢[PRAAx] C.eqv A A
      (al β A B A (al α B A A (C.id1 A))) (C.id1 A)) :
    Γ ⊢[PRAAx] C.eqv A A
      (C.comp A B A
        (al β A B B (C.id1 B))
        (al α B A A (C.id1 A))) (C.id1 A) := by
  have hu := local_yoneda_rep_arrow L NA hA
  have hy := local_yoneda_rep L (B := A) (A := B) (x := A)
    (f := al α B A A (C.id1 A)) NB hB hu
  exact L.eqv_trans (L.eqv_symm hy) hround

/-- The second round-trip component implies `u ∘ v = 1_B`. The pair of
this theorem and `representable_inverse_left` gives uniqueness of a
represented object up to a specified isomorphism, without choosing any
representative from an existential assertion. -/
theorem representable_inverse_right {α β : PTm 4}
    {A B : PTm n}
    (NA : AtLaws C (rep C) α Γ B A)
    (NB : AtLaws C (rep C) β Γ A B)
    (hA : Γ ⊢[PRAAx] C.obj A)
    (hB : Γ ⊢[PRAAx] C.obj B)
    (hround : Γ ⊢[PRAAx] C.eqv B B
      (al α B A B (al β A B B (C.id1 B))) (C.id1 B)) :
    Γ ⊢[PRAAx] C.eqv B B
      (C.comp B A B
        (al α B A A (C.id1 A))
        (al β A B B (C.id1 B))) (C.id1 B) := by
  have hv := local_yoneda_rep_arrow L NB hB
  have hy := local_yoneda_rep L (B := B) (A := A) (x := B)
    (f := al β A B B (C.id1 B)) NA hA hv
  exact L.eqv_trans (L.eqv_symm hy) hround

end CategoryIPRA.Representability
