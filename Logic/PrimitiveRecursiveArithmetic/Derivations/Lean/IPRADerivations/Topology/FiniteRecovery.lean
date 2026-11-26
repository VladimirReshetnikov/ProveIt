import IPRADerivations.Topology.FiniteProductsQuotients
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fintype

/-!
# Recovery of finite topologies, homeomorphisms and discrete-family certificates

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`:

* F02 (`thm:finite-recover`), for coded (Boolean) topology tables `T` on `Fin k` that contain `∅`, `univ` and are
  closed under binary `∩` and `∪`: the specialization relation `x ≼_T y ⇔ ∀ U ∈ T, x ∈ U → y ∈ U` is a preorder
  (`spec_refl`, `spec_trans`); the least open neighbourhood `N_x = ⋂_{x ∈ V ∈ T} V` lies in `T` (`nbhd_mem`, by
  "a bounded fold") and consists of the `y` with `x ≼_T y` (`mem_nbhd`); the upward-closed sets are exactly `T`
  (`upward_iff_mem`, "an upward-closed `U` is the union of `N_x`, `x ∈ U`"); and recovering a preorder from its
  table of upward sets returns the preorder (`recover_preorder`);
* F08 (`thm:finite-homeo`): for a bijection `e`, order embedding in both directions makes the inverse monotone
  (`homeo_symm`), order isomorphisms compose (`homeo_trans`), opens are transported along `e` in both directions
  (`homeo_open`), and the existence of an order isomorphism is decidable by finite search (`homeo_decidable`);
* F24 (`thm:finite-discrete-family`): `↑x` meets `A_i` exactly when `x ∈ Cl A_i` (`up_meets_iff`), so a family
  member class has an open neighbourhood of `x` meeting two members `i ≠ j` only if `Cl A_i x` and `Cl A_j x`
  hold together (`meet_two`), and the identity colouring is proper with at most `r` classes (`colour_proper`).
-/

namespace LeanProofs.IPRA.Topology.FiniteRecovery

open_ipra
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Topology.FiniteInteriorClosure

variable {k : ℕ}

/-! ## F02 -/

/-- A coded topology table. -/
structure Table (T : Finset (Finset (Fin k))) : Prop where
  empty : ∅ ∈ T
  univ : Finset.univ ∈ T
  inter : ∀ U ∈ T, ∀ V ∈ T, U ∩ V ∈ T
  union : ∀ U ∈ T, ∀ V ∈ T, U ∪ V ∈ T

/-- `x ≼_T y`. -/
def spec (T : Finset (Finset (Fin k))) (x y : Fin k) : Prop := ∀ U ∈ T, x ∈ U → y ∈ U

theorem spec_refl (T : Finset (Finset (Fin k))) (x : Fin k) : spec T x x := fun _ _ h => h

theorem spec_trans (T : Finset (Finset (Fin k))) {x y z : Fin k} (h₁ : spec T x y) (h₂ : spec T y z) :
    spec T x z := fun U hU hx => h₂ U hU (h₁ U hU hx)

/-- Finite intersections of members of `T` lie in `T`. -/
theorem inf_mem {T : Finset (Finset (Fin k))} (hT : Table T) (F : Finset (Finset (Fin k))) (hF : F ⊆ T) :
    F.inf id ∈ T := by
  induction F using Finset.induction_on with
  | empty => simpa using hT.univ
  | insert V F hV ih =>
    rw [Finset.inf_insert]
    exact hT.inter _ (hF (Finset.mem_insert_self _ _)) _ (ih fun W hW => hF (Finset.mem_insert_of_mem hW))

/-- Finite unions of members of `T` lie in `T`. -/
theorem sup_mem {T : Finset (Finset (Fin k))} (hT : Table T) (F : Finset (Finset (Fin k))) (hF : F ⊆ T) :
    F.sup id ∈ T := by
  induction F using Finset.induction_on with
  | empty => simpa using hT.empty
  | insert V F hV ih =>
    rw [Finset.sup_insert]
    exact hT.union _ (hF (Finset.mem_insert_self _ _)) _ (ih fun W hW => hF (Finset.mem_insert_of_mem hW))

/-- The least open neighbourhood `N_x`. -/
def nbhd (T : Finset (Finset (Fin k))) (x : Fin k) : Finset (Fin k) := (T.filter (x ∈ ·)).inf id

theorem nbhd_mem {T : Finset (Finset (Fin k))} (hT : Table T) (x : Fin k) : nbhd T x ∈ T :=
  inf_mem hT _ (Finset.filter_subset _ _)

theorem mem_inf_iff (F : Finset (Finset (Fin k))) (y : Fin k) : y ∈ F.inf id ↔ ∀ V ∈ F, y ∈ V := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert V F hV ih =>
    rw [Finset.inf_insert, id, Finset.inf_eq_inter, Finset.mem_inter, ih]
    simp

theorem mem_nbhd (T : Finset (Finset (Fin k))) (x y : Fin k) : y ∈ nbhd T x ↔ spec T x y := by
  rw [nbhd, mem_inf_iff]
  simp only [Finset.mem_filter, spec]
  exact ⟨fun h U hU hx => h U ⟨hU, hx⟩, fun h U hU => h U hU.1 hU.2⟩

/-- Upward-closed sets. -/
def Upward (rel : Fin k → Fin k → Prop) (U : Finset (Fin k)) : Prop := ∀ x ∈ U, ∀ y, rel x y → y ∈ U

/-- The upward-closed sets of `≼_T` are exactly the members of `T`. -/
theorem upward_iff_mem {T : Finset (Finset (Fin k))} (hT : Table T) (U : Finset (Fin k)) :
    Upward (spec T) U ↔ U ∈ T := by
  refine ⟨fun hU => ?_, fun hU x hx y hxy => hxy U hU hx⟩
  have e : U = (U.image (nbhd T)).sup id := by
    ext y
    simp only [Finset.mem_sup, Finset.mem_image, id]
    constructor
    · intro hy
      exact ⟨nbhd T y, ⟨y, hy, rfl⟩, (mem_nbhd T y y).mpr (spec_refl T y)⟩
    · rintro ⟨V, ⟨x, hx, rfl⟩, hy⟩
      exact hU x hx y ((mem_nbhd T x y).mp hy)
  rw [e]
  exact sup_mem hT _ fun V hV => by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hV
    exact nbhd_mem hT x

/-- Recovering a preorder from its table of upward sets returns the preorder. -/
theorem recover_preorder (rel : Fin k → Fin k → Prop) [DecidableRel rel] (hrefl : ∀ x, rel x x)
    (htrans : ∀ x y z, rel x y → rel y z → rel x z) (x y : Fin k) :
    spec ((Finset.univ : Finset (Finset (Fin k))).filter fun U => ∀ a ∈ U, ∀ b, rel a b → b ∈ U) x y ↔
      rel x y := by
  constructor
  · intro h
    have hup : (Finset.univ.filter (rel x ·)) ∈ (Finset.univ : Finset (Finset (Fin k))).filter
        fun U => ∀ a ∈ U, ∀ b, rel a b → b ∈ U := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha b hab
      exact htrans x a b ha hab
    have := h _ hup (by simp [hrefl x])
    simpa using this
  · intro hxy U hU hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact hU x hx y hxy

/-! ## F08 -/

variable {l : ℕ} {rel : Fin k → Fin k → Prop} {rel' : Fin l → Fin l → Prop}

/-- An order isomorphism along a bijection. -/
def IsHomeo (rel : Fin k → Fin k → Prop) (rel' : Fin l → Fin l → Prop) (e : Fin k ≃ Fin l) : Prop :=
  ∀ x y, rel x y ↔ rel' (e x) (e y)

theorem homeo_symm {e : Fin k ≃ Fin l} (h : IsHomeo rel rel' e) : IsHomeo rel' rel e.symm := fun a b => by
  rw [h]; simp

theorem homeo_trans {m : ℕ} {rel'' : Fin m → Fin m → Prop} {e : Fin k ≃ Fin l} {e' : Fin l ≃ Fin m}
    (h : IsHomeo rel rel' e) (h' : IsHomeo rel' rel'' e') : IsHomeo rel rel'' (e.trans e') := fun x y => by
  rw [h, h']; rfl

theorem homeo_refl : IsHomeo rel rel (Equiv.refl (Fin k)) := fun _ _ => Iff.rfl

/-- Opens are transported along an order isomorphism. -/
theorem homeo_open {n : ℕ} {Γ : List (Fm PTm n)} {e : Fin k ≃ Fin l} (h : IsHomeo rel rel' e)
    {U : Fin l → Fm PTm n} (hU : IsOpen rel' Γ U) : IsOpen rel Γ (fun x => U (e x)) :=
  fun x y hxy => hU _ _ ((h x y).mp hxy)

/-- Homeomorphism of finite preorders is decidable by finite search over bijections. -/
noncomputable def homeo_decidable [DecidableRel rel] [DecidableRel rel'] :
    Decidable (∃ e : Fin k ≃ Fin l, IsHomeo rel rel' e) := by
  classical
  exact inferInstance

/-! ## F24 -/

variable {n r : ℕ} {Γ : List (Fm PTm n)} [DecidableRel rel]

/-- `↑x` meets `A`: `⋁_y (y ∈ ↑x ∧ y ∈ A)`. -/
def upMeets (rel : Fin k → Fin k → Prop) [DecidableRel rel] (x : Fin k) (A : Fin k → Fm PTm n) : Fm PTm n :=
  disjFin fun y => LeanProofs.IPRA.Topology.FiniteProductsQuotients.up rel x y ⋏ A y

/-- `↑x` meets `A` exactly when `x ∈ Cl A`. -/
theorem up_meets_iff (x : Fin k) (A : Fin k → Fm PTm n) :
    (Γ ⊢[PRAAx] upMeets rel x A ⟶ Cl rel A x) ∧ (Γ ⊢[PRAAx] Cl rel A x ⟶ upMeets rel x A) := by
  refine ⟨disjFin_imp fun y => ?_, cl_imp fun y hxy => ?_⟩
  · beta_reduce
    unfold LeanProofs.IPRA.Topology.FiniteProductsQuotients.up
    by_cases h : rel x y
    · rw [if_pos h]; exact .impI (cl_intro h Prf.hyp0.andE₂)
    · rw [if_neg h]; exact .impI (.botE _ Prf.hyp0.andE₁)
  · refine .impI (disjFin_intro y ?_)
    beta_reduce
    unfold LeanProofs.IPRA.Topology.FiniteProductsQuotients.up
    rw [if_pos hxy]
    exact .andI (.eqRefl _) Prf.hyp0

/-- A member class has a neighbourhood of `x` meeting two members only when `x ∈ Cl A_i ∩ Cl A_j`; so a class
without an edge (`¬ (Cl A_i x ∧ Cl A_j x)` for `i ≠ j`) is a discrete family. -/
theorem meet_two (A : Fin r → Fin k → Fm PTm n) {x : Fin k} {i j : Fin r}
    (hedge : Γ ⊢[PRAAx] Cl rel (A i) x ⟶ (Cl rel (A j) x ⟶ Fm.bot)) :
    Γ ⊢[PRAAx] upMeets rel x (A i) ⟶ (upMeets rel x (A j) ⟶ Fm.bot) :=
  .impI (.impI (.impE (.impE hedge.wk.wk (.impE (up_meets_iff x (A i)).1.wk.wk Prf.hyp1))
    (.impE (up_meets_iff x (A j)).1.wk.wk Prf.hyp0)))

/-- The identity colouring of the `r` indices is proper and uses at most `r` colours. -/
theorem colour_proper (edge : Fin r → Fin r → Prop) (hirr : ∀ i, ¬ edge i i) :
    (∀ i j, edge i j → (id i : Fin r) ≠ id j) ∧ Fintype.card (Fin r) ≤ r :=
  ⟨fun i j h hij => hirr i (by simp only [id] at hij; subst hij; exact h), by simp⟩

end LeanProofs.IPRA.Topology.FiniteRecovery
