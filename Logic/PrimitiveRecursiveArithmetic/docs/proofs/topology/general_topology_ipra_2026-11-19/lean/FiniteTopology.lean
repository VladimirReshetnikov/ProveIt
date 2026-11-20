import Init

/-!
# Constructive order-theoretic kernel for finite topology

Checked with Lean 4.32.0, using only Init.  There is no `sorry`, `axiom`,
`Classical`, or Mathlib dependency.  The propositions below are constructive
metatheorems.  Restricting the carrier to Fin n and representing relations and
subsets by Boolean tables yields the finite algorithms in the accompanying
chapter.  This file does NOT claim to implement the first-order iPRA syntax,
its proof checker, or the compilation of these proofs to iPRA derivations.

The deliberately generic predicate interface is useful for the elementary
lemmas; the finite Boolean coding and the remaining chapter theorems are
specified in the chapter's formalization roadmap.
-/

namespace FiniteTopology

structure CPreorder (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def Up (P : CPreorder α) (U : α → Prop) : Prop :=
  ∀ {x y}, P.rel x y → U x → U y

def Down (P : CPreorder α) (A : α → Prop) : Prop :=
  ∀ {x y}, P.rel x y → A y → A x

def Interior (P : CPreorder α) (A : α → Prop) (x : α) : Prop :=
  ∀ y, P.rel x y → A y

def Closure (P : CPreorder α) (A : α → Prop) (x : α) : Prop :=
  ∃ y, P.rel x y ∧ A y

def Exterior (P : CPreorder α) (A : α → Prop) : α → Prop :=
  Interior P (fun x => ¬ A x)

theorem up_empty (P : CPreorder α) : Up P (fun _ => False) := by
  intro x y h hfalse
  exact hfalse.elim

theorem up_univ (P : CPreorder α) : Up P (fun _ => True) := by
  intro x y h htrue
  exact htrue

theorem up_inter (P : CPreorder α) {U V : α → Prop}
    (hU : Up P U) (hV : Up P V) : Up P (fun x => U x ∧ V x) := by
  intro x y hxy hx
  exact ⟨hU hxy hx.1, hV hxy hx.2⟩

theorem up_union (P : CPreorder α) {U V : α → Prop}
    (hU : Up P U) (hV : Up P V) : Up P (fun x => U x ∨ V x) := by
  intro x y hxy hx
  cases hx with
  | inl hu => exact Or.inl (hU hxy hu)
  | inr hv => exact Or.inr (hV hxy hv)

theorem up_indexed_union (P : CPreorder α) {U : ι → α → Prop}
    (hU : ∀ i, Up P (U i)) : Up P (fun x => ∃ i, U i x) := by
  intro x y hxy hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, hU i hxy hi⟩

theorem principal_up (P : CPreorder α) (x : α) : Up P (P.rel x) := by
  intro y z hyz hxy
  exact P.trans hxy hyz

theorem interior_up (P : CPreorder α) (A : α → Prop) :
    Up P (Interior P A) := by
  intro x y hxy hx z hyz
  exact hx z (P.trans hxy hyz)

theorem interior_subset (P : CPreorder α) (A : α → Prop) (x : α) :
    Interior P A x → A x := by
  intro hx
  exact hx x (P.refl x)

theorem interior_greatest (P : CPreorder α) {U A : α → Prop}
    (hU : Up P U) (hUA : ∀ x, U x → A x) :
    ∀ x, U x → Interior P A x := by
  intro x hx y hxy
  exact hUA y (hU hxy hx)

theorem interior_idempotent (P : CPreorder α) (A : α → Prop) (x : α) :
    Interior P (Interior P A) x ↔ Interior P A x := by
  constructor
  · exact interior_subset P (Interior P A) x
  · intro hx y hxy z hyz
    exact hx z (P.trans hxy hyz)

theorem interior_inter (P : CPreorder α) (A B : α → Prop) (x : α) :
    Interior P (fun y => A y ∧ B y) x ↔
      Interior P A x ∧ Interior P B x := by
  constructor
  · intro h
    exact ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩
  · intro h y hy
    exact ⟨h.1 y hy, h.2 y hy⟩

theorem closure_down (P : CPreorder α) (A : α → Prop) :
    Down P (Closure P A) := by
  intro x y hxy hy
  obtain ⟨z, hyz, hz⟩ := hy
  exact ⟨z, P.trans hxy hyz, hz⟩

theorem subset_closure (P : CPreorder α) (A : α → Prop) (x : α) :
    A x → Closure P A x := by
  intro hx
  exact ⟨x, P.refl x, hx⟩

theorem closure_least (P : CPreorder α) {A D : α → Prop}
    (hD : Down P D) (hAD : ∀ x, A x → D x) :
    ∀ x, Closure P A x → D x := by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := hx
  exact hD hxy (hAD y hy)

theorem closure_idempotent (P : CPreorder α) (A : α → Prop) (x : α) :
    Closure P (Closure P A) x ↔ Closure P A x := by
  constructor
  · intro hx
    obtain ⟨y, hxy, z, hyz, hz⟩ := hx
    exact ⟨z, P.trans hxy hyz, hz⟩
  · exact subset_closure P (Closure P A) x

theorem closure_union (P : CPreorder α) (A B : α → Prop) (x : α) :
    Closure P (fun y => A y ∨ B y) x ↔
      Closure P A x ∨ Closure P B x := by
  constructor
  · intro hx
    obtain ⟨y, hxy, hy⟩ := hx
    cases hy with
    | inl ha => exact Or.inl ⟨y, hxy, ha⟩
    | inr hb => exact Or.inr ⟨y, hxy, hb⟩
  · intro hx
    cases hx with
    | inl ha =>
      obtain ⟨y, hxy, hy⟩ := ha
      exact ⟨y, hxy, Or.inl hy⟩
    | inr hb =>
      obtain ⟨y, hxy, hy⟩ := hb
      exact ⟨y, hxy, Or.inr hy⟩

theorem exterior_iff_not_closure (P : CPreorder α) (A : α → Prop) (x : α) :
    Exterior P A x ↔ ¬ Closure P A x := by
  constructor
  · intro hx hc
    obtain ⟨y, hxy, hy⟩ := hc
    exact hx y hxy hy
  · intro hx y hxy hy
    exact hx ⟨y, hxy, hy⟩

def Monotone (P : CPreorder α) (Q : CPreorder β) (f : α → β) : Prop :=
  ∀ {x y}, P.rel x y → Q.rel (f x) (f y)

def Continuous (P : CPreorder α) (Q : CPreorder β) (f : α → β) : Prop :=
  ∀ V, Up Q V → Up P (fun x => V (f x))

theorem continuous_iff_monotone (P : CPreorder α) (Q : CPreorder β)
    (f : α → β) : Continuous P Q f ↔ Monotone P Q f := by
  constructor
  · intro hc x y hxy
    exact hc (Q.rel (f x)) (principal_up Q (f x)) hxy (Q.refl (f x))
  · intro hm V hV x y hxy hx
    exact hV (hm hxy) hx

theorem monotone_id (P : CPreorder α) : Monotone P P (fun x => x) := by
  intro x y hxy
  exact hxy

theorem monotone_comp (P : CPreorder α) (Q : CPreorder β)
    (R : CPreorder γ) {f : α → β} {g : β → γ}
    (hf : Monotone P Q f) (hg : Monotone Q R g) :
    Monotone P R (fun x => g (f x)) := by
  intro x y hxy
  exact hg (hf hxy)

theorem monotone_closure_image (P : CPreorder α) (Q : CPreorder β)
    {f : α → β} (hf : Monotone P Q f) (A : α → Prop) (x : α)
    (hx : Closure P A x) :
    Closure Q (fun b => ∃ a, A a ∧ f a = b) (f x) := by
  obtain ⟨y, hxy, hy⟩ := hx
  exact ⟨f y, hf hxy, y, hy, rfl⟩

def Prod (P : CPreorder α) (Q : CPreorder β) : CPreorder (α × β) where
  rel a b := P.rel a.1 b.1 ∧ Q.rel a.2 b.2
  refl a := ⟨P.refl a.1, Q.refl a.2⟩
  trans hxy hyz := ⟨P.trans hxy.1 hyz.1, Q.trans hxy.2 hyz.2⟩

theorem pair_monotone (P : CPreorder α) (Q : CPreorder β)
    (R : CPreorder γ) {f : γ → α} {g : γ → β}
    (hf : Monotone R P f) (hg : Monotone R Q g) :
    Monotone R (Prod P Q) (fun z => (f z, g z)) := by
  intro x y hxy
  exact ⟨hf hxy, hg hxy⟩

structure CMor (P : CPreorder α) (Q : CPreorder β) where
  toFun : α → β
  mono : Monotone P Q toFun

def Maps (P : CPreorder α) (Q : CPreorder β) : CPreorder (CMor P Q) where
  rel f g := ∀ x, Q.rel (f.toFun x) (g.toFun x)
  refl f x := Q.refl (f.toFun x)
  trans hfg hgh x := Q.trans (hfg x) (hgh x)

def evaluation (P : CPreorder α) (Q : CPreorder β) :
    CMor (Prod (Maps P Q) P) Q where
  toFun p := p.1.toFun p.2
  mono := by
    intro a b hab
    exact Q.trans (hab.1 a.2) (b.1.mono hab.2)

def curry (R : CPreorder γ) (P : CPreorder α) (Q : CPreorder β)
    (h : CMor (Prod R P) Q) : CMor R (Maps P Q) where
  toFun z := {
    toFun := fun x => h.toFun (z, x)
    mono := by
      intro x y hxy
      exact h.mono ⟨R.refl z, hxy⟩
  }
  mono := by
    intro z w hzw x
    exact h.mono ⟨hzw, P.refl x⟩

def uncurry (R : CPreorder γ) (P : CPreorder α) (Q : CPreorder β)
    (h : CMor R (Maps P Q)) : CMor (Prod R P) Q where
  toFun p := (h.toFun p.1).toFun p.2
  mono := by
    intro a b hab
    exact Q.trans (h.mono hab.1 a.2) ((h.toFun b.1).mono hab.2)

theorem uncurry_curry_pointwise (R : CPreorder γ) (P : CPreorder α)
    (Q : CPreorder β) (h : CMor (Prod R P) Q) (z : γ) (x : α) :
    (uncurry R P Q (curry R P Q h)).toFun (z, x) = h.toFun (z, x) := rfl

theorem curry_uncurry_pointwise (R : CPreorder γ) (P : CPreorder α)
    (Q : CPreorder β) (h : CMor R (Maps P Q)) (z : γ) (x : α) :
    ((curry R P Q (uncurry R P Q h)).toFun z).toFun x =
      (h.toFun z).toFun x := rfl

abbrev FinRelTable (n : Nat) := Fin n → Fin n → Bool
abbrev FinSubsetTable (n : Nat) := Fin n → Bool

def fromTable {n : Nat} (t : FinRelTable n)
    (hr : ∀ i, t i i = true)
    (ht : ∀ i j k, t i j = true → t j k = true → t i k = true) :
    CPreorder (Fin n) where
  rel i j := t i j = true
  refl := hr
  trans := fun {i j k} hij hjk => ht i j k hij hjk

-- Axiom audit: these statements should report an empty axiom list.

end FiniteTopology

-- Complete theorem axiom audit for this standalone file.
#print axioms FiniteTopology.up_empty
#print axioms FiniteTopology.up_univ
#print axioms FiniteTopology.up_inter
#print axioms FiniteTopology.up_union
#print axioms FiniteTopology.up_indexed_union
#print axioms FiniteTopology.principal_up
#print axioms FiniteTopology.interior_up
#print axioms FiniteTopology.interior_subset
#print axioms FiniteTopology.interior_greatest
#print axioms FiniteTopology.interior_idempotent
#print axioms FiniteTopology.interior_inter
#print axioms FiniteTopology.closure_down
#print axioms FiniteTopology.subset_closure
#print axioms FiniteTopology.closure_least
#print axioms FiniteTopology.closure_idempotent
#print axioms FiniteTopology.closure_union
#print axioms FiniteTopology.exterior_iff_not_closure
#print axioms FiniteTopology.continuous_iff_monotone
#print axioms FiniteTopology.monotone_id
#print axioms FiniteTopology.monotone_comp
#print axioms FiniteTopology.monotone_closure_image
#print axioms FiniteTopology.pair_monotone
#print axioms FiniteTopology.uncurry_curry_pointwise
#print axioms FiniteTopology.curry_uncurry_pointwise
