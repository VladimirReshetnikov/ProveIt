import BusyBeaver.ZFC.QuotientSeparation
import BusyBeaver.ZFC.KQ1Basic

/-! Empty Set, Pairing, Union and singleton-closed containers in the actual CP/GIC quotient
(`KQ1Basic`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientBasic

open ProfileModel

universe u
variable {V : Type u}

theorem quotient_empty (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∃ e, ∀ z, ¬ QuotientModel.quotientMember mem witness h z e :=
  KQ1Basic.quotient_empty mem witness (QuotientModel.ofCPGIC mem witness h)

theorem quotient_pair (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (a b : QuotientModel.Domain mem witness h) :
    ∃ p, ∀ z, QuotientModel.quotientMember mem witness h z p ↔ z = a ∨ z = b :=
  KQ1Basic.quotient_pair mem witness (QuotientModel.ofCPGIC mem witness h) a b

theorem quotient_pair_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ env, Sat (QuotientModel.quotientMember mem witness h) env Pair_form :=
  KQ1Basic.quotient_pair_form mem witness (QuotientModel.ofCPGIC mem witness h)

theorem quotient_union (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (a : QuotientModel.Domain mem witness h) :
    ∃ b, ∀ z, QuotientModel.quotientMember mem witness h z b ↔
      ∃ x, QuotientModel.quotientMember mem witness h z x ∧
        QuotientModel.quotientMember mem witness h x a :=
  KQ1Basic.quotient_union mem witness (QuotientModel.ofCPGIC mem witness h) a

theorem quotient_union_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ env, Sat (QuotientModel.quotientMember mem witness h) env Union_form :=
  KQ1Basic.quotient_union_form mem witness (QuotientModel.ofCPGIC mem witness h)

/-- The empty-root instance, still with singleton rather than von Neumann successors. -/
theorem quotient_empty_singleton_container (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) :
    ∃ v, (∃ e, QuotientModel.quotientMember mem witness h e v ∧
        ∀ z, ¬ QuotientModel.quotientMember mem witness h z e) ∧
      ∀ x, QuotientModel.quotientMember mem witness h x v →
        ∃ s, QuotientModel.quotientMember mem witness h s v ∧
          ∀ z, QuotientModel.quotientMember mem witness h z s ↔ z = x :=
  KQ1Basic.quotient_empty_singleton_container mem witness (QuotientModel.ofCPGIC mem witness h)

end SetTheory.BusyBeaver.ZFC.QuotientBasic
