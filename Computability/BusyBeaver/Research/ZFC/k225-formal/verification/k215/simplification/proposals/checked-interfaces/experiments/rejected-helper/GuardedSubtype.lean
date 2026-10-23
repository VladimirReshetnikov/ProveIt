/-!
Guarded quantification over a subtype. A guard that supports every quantified
coordinate makes restricting the quantifiers to the subtype semantics-preserving.
The statements use no set-theoretic, choice, extensionality or quotient axiom.
-/

namespace GuardedSubtype

universe u
variable {α : Type u} {P : α → Prop}

theorem exists_four (Q : α → α → α → α → Prop)
    (support : ∀ a b c d, Q a b c d → P a ∧ P b ∧ P c ∧ P d) :
    (∃ a b c d : Subtype P, Q a.val b.val c.val d.val) ↔ ∃ a b c d, Q a b c d :=
  ⟨fun ⟨a, b, c, d, h⟩ => ⟨a.val, b.val, c.val, d.val, h⟩,
   fun ⟨a, b, c, d, h⟩ =>
     let hp := support a b c d h
     ⟨⟨a, hp.1⟩, ⟨b, hp.2.1⟩, ⟨c, hp.2.2.1⟩, ⟨d, hp.2.2.2⟩, h⟩⟩

theorem forall_three (G Q : α → α → α → Prop)
    (support : ∀ a b c, G a b c → P a ∧ P b ∧ P c) :
    (∀ a b c : Subtype P, G a.val b.val c.val → Q a.val b.val c.val) ↔
      ∀ a b c, G a b c → Q a b c :=
  ⟨fun h a b c hg =>
     let hp := support a b c hg
     h ⟨a, hp.1⟩ ⟨b, hp.2.1⟩ ⟨c, hp.2.2⟩ hg,
   fun h a b c hg => h a.val b.val c.val hg⟩

end GuardedSubtype
