import IPRADerivations.Foundations.Yoneda

/-!
# Yoneda at a fixed representing object and parameter

Uncompiled integration draft; see ../README.md for verification status.

The upstream `NatLaws` record asks that one term alpha(p,A,x,f) be natural
uniformly in p and A. That is a useful sufficient interface but is stronger
than a single natural transformation at specified p,A. This file localizes
the law record to those terms and to the current object-language context.

All components remain a fixed `PTm 4`; this change does not introduce a
universal evaluator or an internal function space. The law fields and theorem
conclusions are still actual `Prf PRAAx` derivations.
-/

namespace CategoryIPRA.LocalYoneda

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Yoneda
open Syn
open scoped Fm

/-- Laws of one specified transformation `h_A → F_p` under the fixed
object-language hypotheses Γ. They need not hold at other p or A. -/
structure AtLaws (C : Pres) (F : Fam) (α : PTm 4)
    {n : ℕ} (Γ : List (Fm PTm n)) (p A : PTm n) : Prop where
  al_car : ∀ {x f : PTm n},
    (Γ ⊢[PRAAx] C.hom x A f) →
    (Γ ⊢[PRAAx] F.car p x (al α p A x f))
  al_congr : ∀ {x f f' : PTm n},
    (Γ ⊢[PRAAx] C.eqv x A f f') →
    (Γ ⊢[PRAAx] F.sim p x (al α p A x f) (al α p A x f'))
  natural : ∀ {x y k f : PTm n},
    (Γ ⊢[PRAAx] C.hom y x k) → (Γ ⊢[PRAAx] C.hom x A f) →
    (Γ ⊢[PRAAx] F.sim p y
      (al α p A y (C.comp y x A f k))
      (F.ac p y x k (al α p A x f)))

variable {C : Pres} {F : Fam} {α : PTm 4}
variable {n : ℕ} {Γ : List (Fm PTm n)} {p A : PTm n}

theorem from_uniform (N : NatLaws C F α)
    (hp : Γ ⊢[PRAAx] F.par p) (hA : Γ ⊢[PRAAx] C.obj A) :
    AtLaws C F α Γ p A where
  al_car := fun hf => N.al_car hp hA hf
  al_congr := fun h => N.al_congr h
  natural := fun hk hf => N.natural hk hf

theorem local_yoneda (L : C.Laws) (FL : FamLaws C F)
    (N : AtLaws C F α Γ p A) {x f : PTm n}
    (hA : Γ ⊢[PRAAx] C.obj A)
    (hf : Γ ⊢[PRAAx] C.hom x A f) :
    Γ ⊢[PRAAx] F.sim p x (al α p A x f)
      (F.ac p x A f (al α p A A (C.id1 A))) := by
  have hnat := N.natural hf (L.id_hom hA)
  have hunit := N.al_congr (L.id_left hf)
  exact FL.sim_trans (FL.sim_symm hunit) hnat

theorem local_yoneda_element (L : C.Laws)
    (N : AtLaws C F α Γ p A)
    (hA : Γ ⊢[PRAAx] C.obj A) :
    Γ ⊢[PRAAx] F.car p A (al α p A A (C.id1 A)) :=
  N.al_car (L.id_hom hA)

theorem local_yoneda_rep (L : C.Laws) {B x f : PTm n}
    (N : AtLaws C (rep C) α Γ B A)
    (hA : Γ ⊢[PRAAx] C.obj A)
    (hf : Γ ⊢[PRAAx] C.hom x A f) :
    Γ ⊢[PRAAx] C.eqv x B (al α B A x f)
      (C.comp x A B (al α B A A (C.id1 A)) f) := by
  have h := local_yoneda L (rep_laws L) N hA hf
  rw [rep_sim, rep_ac] at h
  exact h

theorem local_yoneda_rep_arrow (L : C.Laws) {B : PTm n}
    (N : AtLaws C (rep C) α Γ B A)
    (hA : Γ ⊢[PRAAx] C.obj A) :
    Γ ⊢[PRAAx] C.hom A B (al α B A A (C.id1 A)) := by
  have h := local_yoneda_element L N hA
  rw [rep_car] at h
  exact h

end CategoryIPRA.LocalYoneda
