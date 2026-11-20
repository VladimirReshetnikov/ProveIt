import Mathlib.Algebra.Order.Field.Basic

/-! First-order translation with named variables and shadowing.
A point variable maps to two different scalar variable names. -/

namespace PlaneTranslation

inductive Axis where | x | y deriving DecidableEq
abbrev Slot := Nat × Axis
abbrev Point (K : Type) := K × K

inductive Term where
  | var (i : Slot) | zero
  | add (s t : Term) | sub (s t : Term) | mul (s t : Term)

def Term.val {K : Type} [Ring K] (ρ : Slot → K) : Term → K
  | .var i => ρ i
  | .zero => 0
  | .add s t => s.val ρ + t.val ρ
  | .sub s t => s.val ρ - t.val ρ
  | .mul s t => s.val ρ * t.val ρ

inductive Logic (Idx Atom : Type) where
  | atom (a : Atom) | bot
  | conj (p q : Logic Idx Atom) | disj (p q : Logic Idx Atom)
  | impl (p q : Logic Idx Atom)
  | ex (i : Idx) (p : Logic Idx Atom) | all (i : Idx) (p : Logic Idx Atom)

def assign {I V : Type} [DecidableEq I] (ρ : I → V) (i : I) (v : V) (j : I) :=
  if i = j then v else ρ j

def holds {I A V : Type} [DecidableEq I] (atom : (I → V) → A → Prop)
    (ρ : I → V) : Logic I A → Prop
  | .atom a => atom ρ a
  | .bot => False
  | .conj p q => holds atom ρ p ∧ holds atom ρ q
  | .disj p q => holds atom ρ p ∨ holds atom ρ q
  | .impl p q => holds atom ρ p → holds atom ρ q
  | .ex i p => ∃ v, holds atom (assign ρ i v) p
  | .all i p => ∀ v, holds atom (assign ρ i v) p

inductive GAtom where
  | eq (a b : Nat) | bet (a p b : Nat) | cong (a b c d : Nat)

inductive SAtom where | eq (s t : Term) | le (s t : Term)
abbrev Geom := Logic Nat GAtom
abbrev Scalar := Logic Slot SAtom

def scalarAtom {K : Type} [Ring K] [LE K] (ρ : Slot → K) : SAtom → Prop
  | .eq s t => s.val ρ = t.val ρ
  | .le s t => s.val ρ ≤ t.val ρ

def diff (a b : Nat) (axis : Axis) :=
  Term.sub (.var (a,axis)) (.var (b,axis))

def squared (a b : Nat) :=
  Term.add (.mul (diff a b .x) (diff a b .x)) (.mul (diff a b .y) (diff a b .y))

def atomTranslation : GAtom → Scalar
  | .eq a b => .conj (.atom (.eq (.var (a,.x)) (.var (b,.x))))
                       (.atom (.eq (.var (a,.y)) (.var (b,.y))))
  | .bet a p b =>
    .conj (.atom (.eq (.mul (diff b a .x) (diff p a .y))
                       (.mul (diff b a .y) (diff p a .x))))
      (.atom (.le (.add (.mul (diff p a .x) (diff p b .x))
                         (.mul (diff p a .y) (diff p b .y))) .zero))
  | .cong a b c d => .atom (.eq (squared a b) (squared c d))

def translate : Geom → Scalar
  | .atom a => atomTranslation a
  | .bot => .bot
  | .conj p q => .conj (translate p) (translate q)
  | .disj p q => .disj (translate p) (translate q)
  | .impl p q => .impl (translate p) (translate q)
  | .ex i p => .ex (i,.x) (.ex (i,.y) (translate p))
  | .all i p => .all (i,.x) (.all (i,.y) (translate p))

def split {K : Type} (ρ : Nat → Point K) : Slot → K
  | (i,.x) => (ρ i).1
  | (i,.y) => (ρ i).2

theorem split_assign {K : Type} (ρ : Nat → Point K) (i : Nat) (x y : K) :
    split (assign ρ i (x,y)) = assign (assign (split ρ) (i,.x) x) (i,.y) y := by
  funext s
  rcases s with ⟨j,a⟩
  cases a <;> by_cases h : i = j <;> simp [split, assign, h]

def d2 {K : Type} [Ring K] (a b : Point K) :=
  (a.1-b.1)*(a.1-b.1) + (a.2-b.2)*(a.2-b.2)

def geomAtom {K : Type} [Ring K] [LE K] (ρ : Nat → Point K) : GAtom → Prop
  | .eq a b => ρ a = ρ b
  | .bet a p b =>
    ((ρ b).1-(ρ a).1)*((ρ p).2-(ρ a).2) = ((ρ b).2-(ρ a).2)*((ρ p).1-(ρ a).1) ∧
    ((ρ p).1-(ρ a).1)*((ρ p).1-(ρ b).1) + ((ρ p).2-(ρ a).2)*((ρ p).2-(ρ b).2) ≤ 0
  | .cong a b c d => d2 (ρ a) (ρ b) = d2 (ρ c) (ρ d)

theorem atom_correct {K : Type} [Ring K] [LE K] (ρ : Nat → Point K) (a : GAtom) :
    geomAtom ρ a ↔ holds scalarAtom (split ρ) (atomTranslation a) := by
  cases a with
  | eq a b => exact Prod.ext_iff
  | bet a p b => rfl
  | cong a b c d => rfl

theorem translate_correct {K : Type} [Ring K] [LE K] (φ : Geom) (ρ : Nat → Point K) :
    holds geomAtom ρ φ ↔ holds scalarAtom (split ρ) (translate φ) := by
  induction φ generalizing ρ with
  | atom a => exact atom_correct ρ a
  | bot => rfl
  | conj p q hp hq => exact and_congr (hp ρ) (hq ρ)
  | disj p q hp hq => exact or_congr (hp ρ) (hq ρ)
  | impl p q hp hq => exact imp_congr (hp ρ) (hq ρ)
  | ex i p hp =>
    constructor
    · rintro ⟨⟨x,y⟩, h⟩
      exact ⟨x,y, split_assign ρ i x y ▸ (hp _).mp h⟩
    · rintro ⟨x,y,h⟩
      exact ⟨(x,y),(hp _).mpr (split_assign ρ i x y ▸ h)⟩
  | all i p hp =>
    constructor
    · intro h x y
      exact split_assign ρ i x y ▸ (hp _).mp (h (x,y))
    · intro h ⟨x,y⟩
      exact (hp _).mpr (split_assign ρ i x y ▸ h x y)

end PlaneTranslation
