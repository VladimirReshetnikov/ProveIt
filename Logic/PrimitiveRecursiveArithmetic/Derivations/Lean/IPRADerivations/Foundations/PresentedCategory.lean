import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Header

/-!
# Primitive-recursively presented categories (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Section "Category theory without a universe of
arbitrary functions". A *fixed presentation* of a category (the first of the packet's three
meanings) consists of formulas and terms of iPRA, fixed before any statement is formed:

* `Obj(a)`: `a` is an object code;
* `Hom(a, b, f)`: `f` is an arrow code `a → b`;
* `Eqv(a, b, f, g)`: the parallel arrows `f`, `g` are equal;
* `idt(a)`: the identity of `a`; `cmp(a, b, d, g, f)`: the composite `g ∘ f : a → d` of
  `f : a → b` and `g : b → d`.

The predicates are arbitrary formulas, so equality of arrows need not be decidable. The laws
of a category are *supplied proofs*: `Pres.Laws C` asserts that each law is derivable in iPRA,
in the form of a rule valid at arbitrary terms and under arbitrary hypotheses (equivalently,
the universally closed implication is a theorem). Nothing quantifies over functions or over
program codes.

For every presentation with laws, the following are derived in iPRA
(Subsection "Elementary categorical results are intuitionistic"):

* `inverse_unique`: a left inverse `g` and a right inverse `h` of `f` are equal,
  `g = g ∘ 1 = g ∘ (f ∘ h) = (g ∘ f) ∘ h = 1 ∘ h = h`; closed form `inverse_unique_closed`;
* `section_monic`: if `r ∘ s = 1` then `s ∘ u = s ∘ v` gives `u = v`;
* `retraction_epic`: if `r ∘ s = 1` then `u ∘ r = v ∘ r` gives `u = v`;
* `monic_split`: if `f ∘ r = 1` and `f` is left cancellable against the pair `(r ∘ f, 1)`, then
  `r ∘ f = 1`: a monic with a right inverse is an isomorphism.

* `terminal_unique`: for two terminal objects, given with their arrows `bang` and the
  uniqueness law (`Terminal`), the composite of the two structure maps is the identity.

`natAdd` is the additive monoid of the natural numbers as a one-object presentation, with its
laws (`natAdd_laws`), so the theorems are not vacuous.

No excluded middle and no induction is used beyond what the supplied laws themselves need.
-/

namespace LeanProofs.IPRA.Foundations.PresentedCategory

open_ipra

/-- A presentation of a category by formulas and terms of iPRA. -/
structure Pres where
  /-- `Obj(a)`; variable `0 = a`. -/
  Obj : Fm PTm 1
  /-- `Hom(a, b, f)`; variables `0 = a`, `1 = b`, `2 = f`. -/
  Hom : Fm PTm 3
  /-- `Eqv(a, b, f, g)`; variables `0 = a`, `1 = b`, `2 = f`, `3 = g`. -/
  Eqv : Fm PTm 4
  /-- The identity `idt(a)`; variable `0 = a`. -/
  idt : PTm 1
  /-- The composite `cmp(a, b, d, g, f) = g ∘ f`; variables `0 = a`, `1 = b`, `2 = d`, `3 = g`,
  `4 = f`. -/
  cmp : PTm 5

namespace Pres

variable (C : Pres) {n : ℕ}

/-- `a` is an object. -/
def obj (a : PTm n) : Fm PTm n := C.Obj.subst ![a]
/-- `f : a → b`. -/
def hom (a b f : PTm n) : Fm PTm n := C.Hom.subst ![a, b, f]
/-- `f = g` as arrows `a → b`. -/
def eqv (a b f g : PTm n) : Fm PTm n := C.Eqv.subst ![a, b, f, g]
/-- The identity of `a`. -/
def id1 (a : PTm n) : PTm n := Syn.subst ![a] C.idt
/-- `g ∘ f : a → d` for `f : a → b`, `g : b → d`. -/
def comp (a b d g f : PTm n) : PTm n := Syn.subst ![a, b, d, g, f] C.cmp

/-- The laws of a category, as derivable rules at arbitrary terms and hypotheses. -/
structure Laws : Prop where
  eqv_refl : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.eqv a b f f)
  eqv_symm : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f g : PTm n},
    (Γ ⊢[PRAAx] C.eqv a b f g) → (Γ ⊢[PRAAx] C.eqv a b g f)
  eqv_trans : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f g h : PTm n},
    (Γ ⊢[PRAAx] C.eqv a b f g) → (Γ ⊢[PRAAx] C.eqv a b g h) → (Γ ⊢[PRAAx] C.eqv a b f h)
  id_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a : PTm n},
    (Γ ⊢[PRAAx] C.obj a) → (Γ ⊢[PRAAx] C.hom a a (C.id1 a))
  comp_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b d f g : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.hom b d g) →
      (Γ ⊢[PRAAx] C.hom a d (C.comp a b d g f))
  comp_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b d f f' g g' : PTm n},
    (Γ ⊢[PRAAx] C.eqv a b f f') → (Γ ⊢[PRAAx] C.eqv b d g g') →
      (Γ ⊢[PRAAx] C.eqv a d (C.comp a b d g f) (C.comp a b d g' f'))
  assoc : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b d e f g h : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.hom b d g) → (Γ ⊢[PRAAx] C.hom d e h) →
      (Γ ⊢[PRAAx] C.eqv a e (C.comp a b e (C.comp b d e h g) f) (C.comp a d e h (C.comp a b d g f)))
  id_left : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.eqv a b (C.comp a b b (C.id1 b) f) f)
  id_right : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.eqv a b (C.comp a a b f (C.id1 a)) f)

end Pres

open Pres

section Elementary

variable {C : Pres} (L : C.Laws) {n : ℕ} {Γ : List (Fm PTm n)}

include L

/-- A left inverse and a right inverse of the same arrow are equal. -/
theorem inverse_unique {a b f g h : PTm n}
    (hf : Γ ⊢[PRAAx] C.hom a b f) (hg : Γ ⊢[PRAAx] C.hom b a g) (hh : Γ ⊢[PRAAx] C.hom b a h)
    (hgf : Γ ⊢[PRAAx] C.eqv a a (C.comp a b a g f) (C.id1 a))
    (hfh : Γ ⊢[PRAAx] C.eqv b b (C.comp b a b f h) (C.id1 b)) : Γ ⊢[PRAAx] C.eqv b a g h := by
  -- `g = g ∘ 1_b`
  have s₁ := L.eqv_symm (L.id_right hg)
  -- `g ∘ 1_b = g ∘ (f ∘ h)`
  have s₂ := L.comp_congr (L.eqv_symm hfh) (L.eqv_refl hg)
  -- `g ∘ (f ∘ h) = (g ∘ f) ∘ h`
  have s₃ := L.eqv_symm (L.assoc hh hf hg)
  -- `(g ∘ f) ∘ h = 1_a ∘ h`
  have s₄ := L.comp_congr (L.eqv_refl hh) hgf
  -- `1_a ∘ h = h`
  have s₅ := L.id_left hh
  exact L.eqv_trans s₁ (L.eqv_trans s₂ (L.eqv_trans s₃ (L.eqv_trans s₄ s₅)))

/-- A section is monic: `r ∘ s = 1` and `s ∘ u = s ∘ v` give `u = v`. -/
theorem section_monic {a b x r s u v : PTm n}
    (hs : Γ ⊢[PRAAx] C.hom a b s) (hr : Γ ⊢[PRAAx] C.hom b a r)
    (hu : Γ ⊢[PRAAx] C.hom x a u) (hv : Γ ⊢[PRAAx] C.hom x a v)
    (hrs : Γ ⊢[PRAAx] C.eqv a a (C.comp a b a r s) (C.id1 a))
    (huv : Γ ⊢[PRAAx] C.eqv x b (C.comp x a b s u) (C.comp x a b s v)) :
    Γ ⊢[PRAAx] C.eqv x a u v := by
  -- `u = 1 ∘ u = (r ∘ s) ∘ u = r ∘ (s ∘ u) = r ∘ (s ∘ v) = (r ∘ s) ∘ v = 1 ∘ v = v`
  have t₁ := L.eqv_symm (L.id_left hu)
  have t₂ := L.comp_congr (L.eqv_refl hu) (L.eqv_symm hrs)
  have t₃ := L.assoc hu hs hr
  have t₄ := L.comp_congr huv (L.eqv_refl hr)
  have t₅ := L.eqv_symm (L.assoc hv hs hr)
  have t₆ := L.comp_congr (L.eqv_refl hv) hrs
  have t₇ := L.id_left hv
  exact L.eqv_trans t₁ (L.eqv_trans t₂ (L.eqv_trans t₃ (L.eqv_trans t₄ (L.eqv_trans t₅
    (L.eqv_trans t₆ t₇)))))

/-- A retraction is epic: `r ∘ s = 1` and `u ∘ r = v ∘ r` give `u = v`. -/
theorem retraction_epic {a b y r s u v : PTm n}
    (hs : Γ ⊢[PRAAx] C.hom a b s) (hr : Γ ⊢[PRAAx] C.hom b a r)
    (hu : Γ ⊢[PRAAx] C.hom a y u) (hv : Γ ⊢[PRAAx] C.hom a y v)
    (hrs : Γ ⊢[PRAAx] C.eqv a a (C.comp a b a r s) (C.id1 a))
    (huv : Γ ⊢[PRAAx] C.eqv b y (C.comp b a y u r) (C.comp b a y v r)) :
    Γ ⊢[PRAAx] C.eqv a y u v := by
  -- `u = u ∘ 1 = u ∘ (r ∘ s) = (u ∘ r) ∘ s = (v ∘ r) ∘ s = v ∘ (r ∘ s) = v ∘ 1 = v`
  have t₁ := L.eqv_symm (L.id_right hu)
  have t₂ := L.comp_congr (L.eqv_symm hrs) (L.eqv_refl hu)
  have t₃ := L.eqv_symm (L.assoc hs hr hu)
  have t₄ := L.comp_congr (L.eqv_refl hs) huv
  have t₅ := L.assoc hs hr hv
  have t₆ := L.comp_congr hrs (L.eqv_refl hv)
  have t₇ := L.id_right hv
  exact L.eqv_trans t₁ (L.eqv_trans t₂ (L.eqv_trans t₃ (L.eqv_trans t₄ (L.eqv_trans t₅
    (L.eqv_trans t₆ t₇)))))

/-- A monic with a right inverse is an isomorphism: from `f ∘ r = 1_b` one gets
`f ∘ (r ∘ f) = f ∘ 1_a`; if `f` cancels on the left in this instance, then `r ∘ f = 1_a`. The
cancellation hypothesis is the instance of monicity that the argument uses. -/
theorem monic_split {a b f r : PTm n}
    (hf : Γ ⊢[PRAAx] C.hom a b f) (hr : Γ ⊢[PRAAx] C.hom b a r)
    (hfr : Γ ⊢[PRAAx] C.eqv b b (C.comp b a b f r) (C.id1 b))
    (hmono : (Γ ⊢[PRAAx] C.eqv a b (C.comp a a b f (C.comp a b a r f)) (C.comp a a b f (C.id1 a))) →
      (Γ ⊢[PRAAx] C.eqv a a (C.comp a b a r f) (C.id1 a))) :
    Γ ⊢[PRAAx] C.eqv a a (C.comp a b a r f) (C.id1 a) := by
  refine hmono ?_
  -- `f ∘ (r ∘ f) = (f ∘ r) ∘ f = 1_b ∘ f = f = f ∘ 1_a`
  have t₁ := L.eqv_symm (L.assoc hf hr hf)
  have t₂ := L.comp_congr (L.eqv_refl hf) hfr
  have t₃ := L.id_left hf
  have t₄ := L.eqv_symm (L.id_right hf)
  exact L.eqv_trans t₁ (L.eqv_trans t₂ (L.eqv_trans t₃ t₄))

/-- Variables: `0 = a`, `1 = b`, `2 = f`, `3 = g`, `4 = h`. -/
abbrev inverseUniqueFormula (C : Pres) : Fm PTm 5 :=
  C.hom (var 0) (var 1) (var 2) ⟶ C.hom (var 1) (var 0) (var 3) ⟶ C.hom (var 1) (var 0) (var 4) ⟶
    C.eqv (var 0) (var 0) (C.comp (var 0) (var 1) (var 0) (var 3) (var 2)) (C.id1 (var 0)) ⟶
    C.eqv (var 1) (var 1) (C.comp (var 1) (var 0) (var 1) (var 2) (var 4)) (C.id1 (var 1)) ⟶
    C.eqv (var 1) (var 0) (var 3) (var 4)

/-- Uniqueness of inverses, as a closed theorem of iPRA for every presentation with laws. -/
theorem inverse_unique_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (inverseUniqueFormula C) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (inverse_unique L (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

end Elementary

/-! ## Terminal objects -/

/-- A terminal object with a parameter: the object `T(p)` and the arrow `bang(p, x) : x → T(p)`.
Variables of `T`: `0 = p`; of `bang`: `0 = p`, `1 = x`. -/
structure Terminal (C : Pres) (T : PTm 1) (bang : PTm 2) : Prop where
  bang_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] C.hom x (Syn.subst ![p] T) (Syn.subst ![p, x] bang))
  bang_unique : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {p x f : PTm n},
    (Γ ⊢[PRAAx] C.hom x (Syn.subst ![p] T) f) →
      (Γ ⊢[PRAAx] C.eqv x (Syn.subst ![p] T) f (Syn.subst ![p, x] bang))

section TerminalUnique

variable {C : Pres} (L : C.Laws) {n : ℕ} {Γ : List (Fm PTm n)}

include L

/-- Two terminal objects are isomorphic by their structure maps: for terminal `t = T(p)` and
`u = T'(p')`, the composite `t → u → t` of the two unique arrows is the identity of `t`. By
symmetry the other composite is the identity of `u`. -/
theorem terminal_unique {T T' : PTm 1} {bang bang' : PTm 2} (hT : Terminal C T bang)
    (hT' : Terminal C T' bang') {p p' : PTm n}
    (ht : Γ ⊢[PRAAx] C.obj (Syn.subst ![p] T)) (hu : Γ ⊢[PRAAx] C.obj (Syn.subst ![p'] T')) :
    Γ ⊢[PRAAx] C.eqv (Syn.subst ![p] T) (Syn.subst ![p] T)
      (C.comp (Syn.subst ![p] T) (Syn.subst ![p'] T') (Syn.subst ![p] T)
        (Syn.subst ![p, Syn.subst ![p'] T'] bang) (Syn.subst ![p', Syn.subst ![p] T] bang'))
      (C.id1 (Syn.subst ![p] T)) := by
  -- both sides are arrows `t → t`, hence equal to `bang(p, t)`
  have h₁ := hT.bang_unique (L.comp_hom (hT'.bang_hom (p := p') ht) (hT.bang_hom (p := p) hu))
  have h₂ := hT.bang_unique (L.id_hom ht)
  exact L.eqv_trans h₁ (L.eqv_symm h₂)

end TerminalUnique

/-! ## The additive monoid of the natural numbers as a one-object category -/

/-- One object `0`; arrows are natural numbers, composed by addition. -/
def natAdd : Pres where
  Obj := (var 0 : PTm 1) ≐ zero
  Hom := ((var 0 : PTm 3) ≐ zero) ⋏ ((var 1 : PTm 3) ≐ zero)
  Eqv := (var 2 : PTm 4) ≐ var 3
  idt := zero
  cmp := (var 3 : PTm 5) + var 4

section NatAdd

variable {n : ℕ}

theorem natAdd_obj (a : PTm n) : natAdd.obj a = (a ≐ zero) := by
  simp [Pres.obj, natAdd]

theorem natAdd_hom (a b f : PTm n) : natAdd.hom a b f = ((a ≐ zero) ⋏ (b ≐ zero)) := by
  simp [Pres.hom, natAdd]

theorem natAdd_eqv (a b f g : PTm n) : natAdd.eqv a b f g = (f ≐ g) := by
  simp [Pres.eqv, natAdd]

theorem natAdd_id (a : PTm n) : natAdd.id1 a = zero := by
  simp [Pres.id1, natAdd]

theorem natAdd_comp (a b d g f : PTm n) : natAdd.comp a b d g f = g + f := by
  simp [Pres.comp, natAdd]

/-- The category laws of the additive monoid. -/
theorem natAdd_laws : natAdd.Laws where
  eqv_refl := fun _ => by rw [natAdd_eqv]; exact .eqRefl _
  eqv_symm := fun h => by rw [natAdd_eqv] at h ⊢; exact h.eqSymm
  eqv_trans := fun h₁ h₂ => by rw [natAdd_eqv] at h₁ h₂ ⊢; exact h₁.eqTrans h₂
  id_hom := fun h => by rw [natAdd_obj] at h; rw [natAdd_hom]; exact .andI h h
  comp_hom := fun h₁ h₂ => by
    rw [natAdd_hom] at h₁ h₂ ⊢
    exact .andI (.andE₁ h₁) (.andE₂ h₂)
  comp_congr := fun h₁ h₂ => by
    rw [natAdd_eqv] at h₁ h₂ ⊢
    rw [natAdd_comp, natAdd_comp]
    exact congrAdd h₂ h₁
  assoc := fun _ _ _ => by
    rw [natAdd_eqv]
    simp only [natAdd_comp]
    exact add_assoc _ _ _
  id_left := fun _ => by
    rw [natAdd_eqv, natAdd_comp, natAdd_id]
    exact zero_add _
  id_right := fun _ => by
    rw [natAdd_eqv, natAdd_comp, natAdd_id]
    exact add_zero _

end NatAdd

end LeanProofs.IPRA.Foundations.PresentedCategory
