import BusyBeaver.ZFC.QuotientSeparation

/-! The actual quotient Power Set axiom from the existing CP/GIC model (`KQ1Power`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientPower

open ProfileAxioms ProfileModel

universe u
variable {V : Type u}

/-- Quantification over all quotient elements is exactly interpreted subset. -/
theorem quotient_sub (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (x a : V) :
    SetTheory.Sub (QuotientModel.quotientMember mem witness h)
      (QuotientModel.mk mem witness h x) (QuotientModel.mk mem witness h a) ↔
      InterpretedSub mem x a :=
  KQ1Power.quotient_sub mem witness (QuotientModel.ofCPGIC mem witness h) x a

/-- Power Set in the actual quotient, with every quotient subset included. -/
theorem quotient_power (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (a : QuotientModel.Domain mem witness h) :
    ∃ p, ∀ x, QuotientModel.quotientMember mem witness h x p ↔
      SetTheory.Sub (QuotientModel.quotientMember mem witness h) x a :=
  KQ1Power.quotient_power mem witness (QuotientModel.ofCPGIC mem witness h) a

/-- The repository's actual Power Set formula holds under every valuation. -/
theorem quotient_pow_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ env, SetTheory.Sat (QuotientModel.quotientMember mem witness h) env Pow_form :=
  KQ1Power.quotient_pow_form mem witness (QuotientModel.ofCPGIC mem witness h)

end SetTheory.BusyBeaver.ZFC.QuotientPower
