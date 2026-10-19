import Foundation.Vorspiel.ExistsUnique

#print axioms Classical.choose!_spec
#print axioms Classical.choose_uniq
#print axioms Classical.extendedchoose!_spec
#print axioms Classical.extendedchoose!_spec_not
#print axioms Classical.extendedChoose!_eq_iff

example {α : Sort*} {p : α → Prop} (h : ∃! x, p x) :
    p (Classical.choose! h) := Classical.choose!_spec h

example {α : Sort*} {p : α → Prop} (h : ∃! x, p x) {x : α} (hx : p x) :
    x = Classical.choose! h := Classical.choose_uniq h hx

example {α : Sort*} {p : α → Prop} {r : α → α → Prop}
    (h : ∀ x, p x → ∃! y, r x y) (default : α) {x : α} (hx : p x) :
    r x (Classical.extendedChoose! h default x) :=
  Classical.extendedchoose!_spec h default hx

example {α : Sort*} {p : α → Prop} {r : α → α → Prop}
    (h : ∀ x, p x → ∃! y, r x y) (default : α) {x : α} (hx : ¬p x) :
    Classical.extendedChoose! h default x = default :=
  Classical.extendedchoose!_spec_not h default hx

example {α : Sort*} {p : α → Prop} {r : α → α → Prop}
    (h : ∀ x, p x → ∃! y, r x y) (default : α) {x y : α} (hx : p x) :
    y = Classical.extendedChoose! h default x ↔ r x y :=
  Classical.extendedChoose!_eq_iff h default hx
