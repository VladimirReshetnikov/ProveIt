/- Point-language definitions used in the frame interpretation.
   Lean 4 core. No choice is used to turn a functional relation into data. -/
namespace PlanarIPRA.FrameRelations

universe u v

structure Geometry (Point : Type u) where
  bet : Point → Point → Point → Prop
  cong : Point → Point → Point → Point → Prop

namespace Geometry

variable {Point : Type u} (g : Geometry Point)

def col (a b c : Point) : Prop :=
  g.bet a b c ∨ g.bet b c a ∨ g.bet c a b

def mid (a m b : Point) : Prop := g.bet a m b ∧ g.cong a m m b

def displacement (a b c d : Point) : Prop :=
  ∃ m, g.mid a m d ∧ g.mid b m c

def direction (p q c d : Point) : Prop :=
  c ≠ d ∧ ∃ e, g.displacement c d p e ∧ g.col p e q

def frame (o i j : Point) : Prop :=
  o ≠ i ∧ g.cong o i o j ∧ ∃ i', g.mid i o i' ∧ g.cong j i j i'

def Axis (o i : Point) := {p : Point // g.col o i p}

def transfer (o i j : Point) (x : g.Axis o i) (v : Point) : Prop :=
  g.col o j v ∧ g.direction x.val v i j

def add (o i : Point) (x y z : g.Axis o i) : Prop :=
  g.displacement o x.val y.val z.val

def mul (o i j : Point) (x y z : g.Axis o i) : Prop :=
  ∃ v w, g.transfer o i j y v ∧ g.transfer o i j z w ∧ g.direction x.val w i v

def nonnegative (o i : Point) (z : g.Axis o i) : Prop :=
  g.bet o z.val i ∨ g.bet o i z.val

def le (o i : Point) (x y : g.Axis o i) : Prop :=
  ∃ z, g.add o i x z y ∧ g.nonnegative o i z

def coords (o i j : Point) (p : Point) (xy : g.Axis o i × g.Axis o i) : Prop :=
  ∃ v, g.transfer o i j xy.2 v ∧ g.displacement o xy.1.val v p

end Geometry

/-- The four clauses of "the relation is a bijection" can be used
    intuitionistically without a global choice function. -/
structure BiGraph {A : Type u} {B : Type v} (r : A → B → Prop) : Prop where
  total : ∀ a, ∃ b, r a b
  onto : ∀ b, ∃ a, r a b
  functional : ∀ {a b b'}, r a b → r a b' → b = b'
  injective : ∀ {a a' b}, r a b → r a' b → a = a'

namespace BiGraph

variable {A : Type u} {B : Type v} {r : A → B → Prop} (h : BiGraph r)

include h

theorem pointRoundTrip (a a' : A) : (∃ b, r a b ∧ r a' b) ↔ a = a' := by
  constructor
  · rintro ⟨b, hab, hab'⟩
    exact h.injective hab hab'
  · rintro rfl
    obtain ⟨b, hab⟩ := h.total a
    exact ⟨b, hab, hab⟩

theorem pairRoundTrip (b b' : B) : (∃ a, r a b ∧ r a b') ↔ b = b' := by
  constructor
  · rintro ⟨a, hab, hab'⟩
    exact h.functional hab hab'
  · rintro rfl
    obtain ⟨a, hab⟩ := h.onto b
    exact ⟨a, hab, hab⟩

variable {P : A → Prop} {Q : B → Prop}

theorem exists_transfer (agree : ∀ {a b}, r a b → (P a ↔ Q b)) :
    (∃ a, P a) ↔ ∃ b, Q b := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hab⟩ := h.total a
    exact ⟨b, (agree hab).mp ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, hab⟩ := h.onto b
    exact ⟨a, (agree hab).mpr hb⟩

theorem forall_transfer (agree : ∀ {a b}, r a b → (P a ↔ Q b)) :
    (∀ a, P a) ↔ ∀ b, Q b := by
  constructor
  · intro hp b
    obtain ⟨a, hab⟩ := h.onto b
    exact (agree hab).mp (hp a)
  · intro hq a
    obtain ⟨b, hab⟩ := h.total a
    exact (agree hab).mpr (hq b)

end BiGraph

end PlanarIPRA.FrameRelations
