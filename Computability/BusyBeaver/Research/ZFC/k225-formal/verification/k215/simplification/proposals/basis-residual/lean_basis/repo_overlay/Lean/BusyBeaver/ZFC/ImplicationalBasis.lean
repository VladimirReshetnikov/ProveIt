import BusyBeaver.ZFC.DominatedImplication

/-!
Pure implicational basis, shared with the dominated-row proof.

An unrestricted implicational system satisfies the restricted interface with
the universal relation `below := fun _ _ => True`.  This uses no assumption on
the representation of formulas, no truth constant and no decoder.
The public declarations have the original `Lukasiewicz` names and types.
-/

namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz

universe u
variable {α : Type u}

/-- Only the actual implicational row and its inference rule. -/
structure Implicational (imp : α → α → α) (T : α → Prop) : Prop where
  mp : ∀ {a b}, T (imp a b) → T a → T b
  rho8 : ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))

variable {imp : α → α → α} {T : α → Prop}

private def language (imp : α → α → α) : DominatedImplication.Language α where
  imp := imp
  below := fun _ _ => True
  refl := fun _ => True.intro
  grow_left := fun _ _ => True.intro
  grow_right := fun _ _ => True.intro

private theorem restricted (h : Implicational imp T) :
    DominatedImplication.Restricted (language imp) T where
  mp := h.mp
  rho8 := fun a b c u _ => h.rho8 c u a b

/-- K follows from rho8 alone. -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  DominatedImplication.basisK (restricted h) a b

/-- Peirce follows from rho8 alone. -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) :=
  DominatedImplication.basisPeirce (restricted h) a b

/-- Implication composition. -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) :=
  DominatedImplication.composition (restricted h) a b c

/-- S follows from rho8 alone. -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) :=
  DominatedImplication.basisS (restricted h) a b c

#print axioms k
#print axioms peirce
#print axioms composition
#print axioms s

end SetTheory.BusyBeaver.ZFC.Lukasiewicz
