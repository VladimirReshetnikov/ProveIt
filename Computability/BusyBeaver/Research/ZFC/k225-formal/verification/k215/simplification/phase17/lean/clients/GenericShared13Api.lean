import BusyBeaver.ZFC.DominatedImplication

namespace GenericShared13Api
open SetTheory.BusyBeaver.ZFC
universe v

variable {A : Type v} {L : DominatedImplication.Language A} {T : A → Prop}

theorem unrestricted (h : DominatedImplication.Restricted L T) (a b c u : A) :
    T (L.imp (L.imp (L.imp c u) a) (L.imp (L.imp a c) (L.imp b c))) :=
  DominatedImplication.rho8_all h a b c u

theorem composition (h : DominatedImplication.Restricted L T) (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  DominatedImplication.composition h a b c

theorem lifting (h : DominatedImplication.Restricted L T) {a b : A}
    (hab : T (L.imp a b)) (x : A) :
    T (L.imp (L.imp x a) (L.imp x b)) :=
  DominatedImplication.lift_right h hab x

/-- No chosen element, truth premise, bottom, transitivity or injectivity is supplied. -/
theorem only_explicit_fields (imp : A → A → A) (below : A → A → Prop)
    (refl : ∀ a, below a a)
    (growLeft : ∀ {u x : A} (y : A), below u x → below u (imp x y))
    (growRight : ∀ {u y : A} (x : A), below u y → below u (imp x y))
    (mp : ∀ {a b : A}, T (imp a b) → T a → T b)
    (row : ∀ a b c u : A, below u a →
      T (imp (imp (imp c u) a) (imp (imp a c) (imp b c))))
    (a b c u : A) :
    T (imp (imp (imp c u) a) (imp (imp a c) (imp b c))) :=
  DominatedImplication.rho8_all
    (L := {imp := imp, below := below, refl := refl,
           grow_left := growLeft, grow_right := growRight})
    {mp := mp, rho8 := row} a b c u

theorem k (h : DominatedImplication.Restricted L T) (a b : A) :
    T (L.imp a (L.imp b a)) := DominatedImplication.k h a b

theorem peirce (h : DominatedImplication.Restricted L T) (a b : A) :
    T (L.imp (L.imp (L.imp a b) a) a) := DominatedImplication.peirce h a b

theorem s (h : DominatedImplication.Restricted L T) (a b c : A) :
    T (L.imp (L.imp a (L.imp b c)) (L.imp (L.imp a b) (L.imp a c))) :=
  DominatedImplication.s h a b c

#print axioms unrestricted
#print axioms composition
#print axioms lifting
#print axioms only_explicit_fields
#print axioms k
#print axioms peirce
#print axioms s
end GenericShared13Api
