import IPRADerivations.Foundations.PresentedCategory
import IPRADerivations.Core.Header

/-!
# Presentation-wise Yoneda (`ipra_categorical_methods`, Subsection "Yoneda as a first-order calculation")

Packet: `foundations/ipra_categorical_methods`, the theorem "Presentation-wise Yoneda". Let `C`
be a presented category with laws (`PresentedCategory`).

A *contravariant presented family* `F` (`Fam`, with a parameter `p`) consists of a carrier
formula `Car(p, x, u)` ("`u ∈ F_p(x)`"), an equivalence formula `Sim(p, x, u, v)` and an action
term `act(p, x, y, f, u)` ("`F(f, u) ∈ F_p(x)` for `f : x → y`, `u ∈ F_p(y)`"). Its laws
(`FamLaws`, the packet's (F)) are supplied iPRA proofs, as rules: the action respects the
equivalences, `F(1_x, u) ≃ u` and `F(g ∘ f, u) ≃ F(f, F(g, u))`.

A *specified natural transformation* `α : h_A → F` is a term `α(p, A, x, f)` with the laws
`NatLaws` (the packet's (N)): `α(y, f ∘ k) ≃ F(k, α(x, f))` for `k : y → x`, `f : x → A`.

Derived in iPRA, for every such data:

* `yoneda` ((Y)): `α(x, f) ≃ F(f, α(A, 1_A))` for `f : x → A`; closed form `yoneda_closed`;
* `repr_natural`, `repr_eval` (the converse): for `a ∈ F(A)` the family `α^a(x, f) = F(f, a)`
  is natural, and `α^a(A, 1_A) ≃ a`;
* `rep C` is the representable family `h_p(x) = C(x, p)` with precomposition as action; its
  laws `rep_laws` follow from the category laws;
* `yoneda_rep` (full faithfulness, presentation-wise): a specified natural transformation
  `α : h_A → h_B` satisfies `α(x, f) = a ∘ f` with `a = α(A, 1_A) : A → B`
  (`yoneda_rep_arrow`).

Evaluation at `1_A` and the construction `a ↦ α^a` are thus inverse up to the specified
equivalences: one round trip is `repr_eval`, the other is `yoneda`. No function
extensionality is needed, pointwise equivalence being the equality of transformations.

`idNat` is the identity transformation of the additive monoid `natAdd`, with its laws, as a
concrete instance.

The finite-table version (a single theorem about codes of functors and transformations), the
functor categories, exponentials of finite sets and Kan extensions of the packet are not
derived.
-/

namespace LeanProofs.IPRA.Foundations.Yoneda

open_ipra
open LeanProofs.IPRA.Foundations.PresentedCategory

/-- A contravariant presented family with a parameter. -/
structure Fam where
  /-- The parameter guard `Par(p)`; variable `0 = p`. -/
  Par : Fm PTm 1
  /-- `Car(p, x, u)`: `u ∈ F_p(x)`; variables `0 = p`, `1 = x`, `2 = u`. -/
  Car : Fm PTm 3
  /-- `Sim(p, x, u, v)`: `u ≃ v` in `F_p(x)`; variables `0 = p`, `1 = x`, `2 = u`, `3 = v`. -/
  Sim : Fm PTm 4
  /-- `act(p, x, y, f, u) = F(f, u)`; variables `0 = p`, `1 = x`, `2 = y`, `3 = f`, `4 = u`. -/
  act : PTm 5

namespace Fam

variable (F : Fam) {n : ℕ}

def par (p : PTm n) : Fm PTm n := F.Par.subst ![p]
def car (p x u : PTm n) : Fm PTm n := F.Car.subst ![p, x, u]
def sim (p x u v : PTm n) : Fm PTm n := F.Sim.subst ![p, x, u, v]
def ac (p x y f u : PTm n) : PTm n := Syn.subst ![p, x, y, f, u] F.act

end Fam

/-- The laws (F) of a family over the presented category `C`. -/
structure FamLaws (C : Pres) (F : Fam) : Prop where
  sim_symm : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x u v : PTm n},
    (Γ ⊢[PRAAx] F.sim p x u v) → (Γ ⊢[PRAAx] F.sim p x v u)
  sim_trans : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x u v w : PTm n},
    (Γ ⊢[PRAAx] F.sim p x u v) → (Γ ⊢[PRAAx] F.sim p x v w) → (Γ ⊢[PRAAx] F.sim p x u w)
  act_car : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x y f u : PTm n},
    (Γ ⊢[PRAAx] C.hom x y f) → (Γ ⊢[PRAAx] F.car p y u) → (Γ ⊢[PRAAx] F.car p x (F.ac p x y f u))
  act_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x y f f' u u' : PTm n},
    (Γ ⊢[PRAAx] C.eqv x y f f') → (Γ ⊢[PRAAx] F.sim p y u u') →
      (Γ ⊢[PRAAx] F.sim p x (F.ac p x y f u) (F.ac p x y f' u'))
  act_id : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x u : PTm n},
    (Γ ⊢[PRAAx] F.car p x u) → (Γ ⊢[PRAAx] F.sim p x (F.ac p x x (C.id1 x) u) u)
  act_comp : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x y z f g u : PTm n},
    (Γ ⊢[PRAAx] C.hom x y f) → (Γ ⊢[PRAAx] C.hom y z g) → (Γ ⊢[PRAAx] F.car p z u) →
      (Γ ⊢[PRAAx] F.sim p x (F.ac p x z (C.comp x y z g f) u) (F.ac p x y f (F.ac p y z g u)))

/-- The component `α(p, A, x, f)` of a transformation term; variables `0 = p`, `1 = A`,
`2 = x`, `3 = f`. -/
def al {n : ℕ} (α : PTm 4) (p A x f : PTm n) : PTm n := Syn.subst ![p, A, x, f] α

/-- The laws (N) of a specified natural transformation `h_A → F_p`. -/
structure NatLaws (C : Pres) (F : Fam) (α : PTm 4) : Prop where
  al_car : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p A x f : PTm n},
    (Γ ⊢[PRAAx] F.par p) → (Γ ⊢[PRAAx] C.obj A) → (Γ ⊢[PRAAx] C.hom x A f) →
      (Γ ⊢[PRAAx] F.car p x (al α p A x f))
  al_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p A x f f' : PTm n},
    (Γ ⊢[PRAAx] C.eqv x A f f') → (Γ ⊢[PRAAx] F.sim p x (al α p A x f) (al α p A x f'))
  natural : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p A x y k f : PTm n},
    (Γ ⊢[PRAAx] C.hom y x k) → (Γ ⊢[PRAAx] C.hom x A f) →
      (Γ ⊢[PRAAx] F.sim p y (al α p A y (C.comp y x A f k)) (F.ac p y x k (al α p A x f)))

section Yoneda

variable {C : Pres} {F : Fam} {α : PTm 4} {n : ℕ} {Γ : List (Fm PTm n)}

/-- (Y): `α(x, f) ≃ F(f, α(A, 1_A))` for `f : x → A`. -/
theorem yoneda (L : C.Laws) (FL : FamLaws C F) (N : NatLaws C F α) {p A x f : PTm n}
    (hA : Γ ⊢[PRAAx] C.obj A) (hf : Γ ⊢[PRAAx] C.hom x A f) :
    Γ ⊢[PRAAx] F.sim p x (al α p A x f) (F.ac p x A f (al α p A A (C.id1 A))) := by
  -- (N) at `k = f`, `f = 1_A`: `α(x, 1_A ∘ f) ≃ F(f, α(A, 1_A))`
  have nat := N.natural (p := p) hf (L.id_hom hA)
  -- `1_A ∘ f = f`, and `α` respects equality of arrows
  have c := N.al_congr (p := p) (L.id_left hf)
  exact FL.sim_trans (FL.sim_symm c) nat

/-- The element `a = α(A, 1_A)` lies in `F_p(A)`. -/
theorem yoneda_element (L : C.Laws) (N : NatLaws C F α) {p A : PTm n}
    (hp : Γ ⊢[PRAAx] F.par p) (hA : Γ ⊢[PRAAx] C.obj A) :
    Γ ⊢[PRAAx] F.car p A (al α p A A (C.id1 A)) :=
  N.al_car hp hA (L.id_hom hA)

/-- The converse: `α^a(x, f) = F(f, a)` is natural. -/
theorem repr_natural (FL : FamLaws C F) {p A x y k f a : PTm n} (hk : Γ ⊢[PRAAx] C.hom y x k)
    (hf : Γ ⊢[PRAAx] C.hom x A f) (ha : Γ ⊢[PRAAx] F.car p A a) :
    Γ ⊢[PRAAx] F.sim p y (F.ac p y A (C.comp y x A f k) a) (F.ac p y x k (F.ac p x A f a)) :=
  FL.act_comp hk hf ha

/-- The converse: `α^a(A, 1_A) ≃ a`. -/
theorem repr_eval (FL : FamLaws C F) {p A a : PTm n} (ha : Γ ⊢[PRAAx] F.car p A a) :
    Γ ⊢[PRAAx] F.sim p A (F.ac p A A (C.id1 A) a) a :=
  FL.act_id ha

/-- Variables: `0 = p`, `1 = A`, `2 = x`, `3 = f`. -/
abbrev yonedaFormula (C : Pres) (F : Fam) (α : PTm 4) : Fm PTm 4 :=
  C.obj (var 1) ⟶ C.hom (var 2) (var 1) (var 3) ⟶
    F.sim (var 0) (var 2) (al α (var 0) (var 1) (var 2) (var 3))
      (F.ac (var 0) (var 2) (var 1) (var 3) (al α (var 0) (var 1) (var 1) (C.id1 (var 1))))

/-- The Yoneda identity (Y), as a closed theorem of iPRA for every presented category, family
and specified natural transformation with their laws. -/
theorem yoneda_closed (L : C.Laws) (FL : FamLaws C F) (N : NatLaws C F α) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (yonedaFormula C F α) :=
  closeUniv 4 (.impI (.impI (yoneda L FL N Prf.hyp1 Prf.hyp0)))

end Yoneda

/-! ## Representable families -/

/-- The representable family `h_p(x) = C(x, p)`, with precomposition as action. -/
def rep (C : Pres) : Fam where
  Par := C.Obj
  Car := C.Hom.subst ![var 1, var 0, var 2]
  Sim := C.Eqv.subst ![var 1, var 0, var 2, var 3]
  act := Syn.subst ![var 1, var 2, var 0, var 4, var 3] C.cmp

section Rep

variable (C : Pres) {n : ℕ} {Γ : List (Fm PTm n)}

theorem rep_par (p : PTm n) : (rep C).par p = C.obj p := rfl

theorem rep_car (p x u : PTm n) : (rep C).car p x u = C.hom x p u := by
  simp only [Fam.car, rep, Pres.hom, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem rep_sim (p x u v : PTm n) : (rep C).sim p x u v = C.eqv x p u v := by
  simp only [Fam.sim, rep, Pres.eqv, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem rep_ac (p x y f u : PTm n) : (rep C).ac p x y f u = C.comp x y p u f := by
  simp only [Fam.ac, rep, Pres.comp, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

variable {C}

/-- The representable family satisfies the laws (F). -/
theorem rep_laws (L : C.Laws) : FamLaws C (rep C) where
  sim_symm := fun h => by rw [rep_sim] at h ⊢; exact L.eqv_symm h
  sim_trans := fun h₁ h₂ => by rw [rep_sim] at h₁ h₂ ⊢; exact L.eqv_trans h₁ h₂
  act_car := fun hf hu => by
    rw [rep_car] at hu ⊢; rw [rep_ac]
    exact L.comp_hom hf hu
  act_congr := fun hf hu => by
    rw [rep_sim] at hu ⊢; rw [rep_ac, rep_ac]
    exact L.comp_congr hf hu
  act_id := fun hu => by
    rw [rep_car] at hu; rw [rep_sim, rep_ac]
    exact L.id_right hu
  act_comp := fun hf hg hu => by
    rw [rep_car] at hu; rw [rep_sim]; simp only [rep_ac]
    exact L.eqv_symm (L.assoc hf hg hu)

/-- Full faithfulness, presentation-wise: a natural transformation `α : h_A → h_B` is
composition with the arrow `α(A, 1_A)`. -/
theorem yoneda_rep (L : C.Laws) {α : PTm 4} (N : NatLaws C (rep C) α) {B A x f : PTm n}
    (hA : Γ ⊢[PRAAx] C.obj A) (hf : Γ ⊢[PRAAx] C.hom x A f) :
    Γ ⊢[PRAAx] C.eqv x B (al α B A x f) (C.comp x A B (al α B A A (C.id1 A)) f) := by
  have y := yoneda (Γ := Γ) L (rep_laws L) N (p := B) hA hf
  rw [rep_sim, rep_ac] at y
  exact y

/-- The inducing arrow `α(A, 1_A) : A → B`. -/
theorem yoneda_rep_arrow (L : C.Laws) {α : PTm 4} (N : NatLaws C (rep C) α) {B A : PTm n}
    (hB : Γ ⊢[PRAAx] C.obj B) (hA : Γ ⊢[PRAAx] C.obj A) :
    Γ ⊢[PRAAx] C.hom A B (al α B A A (C.id1 A)) := by
  have h := yoneda_element (Γ := Γ) (F := rep C) L N (p := B) (by rw [rep_par]; exact hB) hA
  rw [rep_car] at h
  exact h

end Rep

/-! ## An instance: the identity transformation of the additive monoid -/

/-- `α(p, A, x, f) = f`. -/
def idNat : PTm 4 := var 3

theorem al_idNat {n : ℕ} (p A x f : PTm n) : al idNat p A x f = f := by simp [al, idNat]

/-- The identity is a natural transformation `h_A → h_p` of the additive monoid. -/
theorem idNat_laws : NatLaws natAdd (rep natAdd) idNat where
  al_car := fun hp _ hf => by
    rw [rep_par, natAdd_obj] at hp
    rw [natAdd_hom] at hf
    rw [rep_car, natAdd_hom]
    exact .andI (.andE₁ hf) hp
  al_congr := fun h => by
    rw [natAdd_eqv] at h
    rw [rep_sim, natAdd_eqv, al_idNat, al_idNat]
    exact h
  natural := fun _ _ => by
    rw [rep_sim, natAdd_eqv, rep_ac, al_idNat, al_idNat, natAdd_comp, natAdd_comp]
    exact Prf.eqRefl _

/-- The Yoneda identity for this instance: one closed sentence of iPRA with all hypotheses
discharged. -/
theorem yoneda_natAdd :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (yonedaFormula natAdd (rep natAdd) idNat) :=
  yoneda_closed natAdd_laws (rep_laws natAdd_laws) idNat_laws

end LeanProofs.IPRA.Foundations.Yoneda
