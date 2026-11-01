import BusyBeaver.ZFC.InductiveAttemptsCore
import BusyBeaver.ZFC.FiniteSets
import BusyBeaver.ZFC.QuotientReplacement

namespace SetTheory.BusyBeaver.ZFC.InductiveAttempts

open SingletonInfinity

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem quotientFiniteBase (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    FiniteSets.Base (QuotientModel.quotientMember rawMem witness h) :=
  FiniteSets.quotientBase rawMem witness h

/-- The actual CP/GIC quotient has an ordinary inductive set. All formula
resources above are instantiated by its checked first-order schemas. -/
theorem quotient_infinity (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    ∃ I, (∃ e0, QuotientModel.quotientMember rawMem witness h e0 I ∧
        ∀ z, ¬ QuotientModel.quotientMember rawMem witness h z e0) ∧
      ∀ x, QuotientModel.quotientMember rawMem witness h x I →
        ∃ sx, QuotientModel.quotientMember rawMem witness h sx I ∧
          ∀ t, QuotientModel.quotientMember rawMem witness h t sx ↔
            QuotientModel.quotientMember rawMem witness h t x ∨ t = x := by
  obtain ⟨Y, ⟨e, heY, he⟩, hY⟩ :=
    QuotientBasic.quotient_empty_singleton_container rawMem witness h
  apply ordinary_infinity_of_container (quotientFiniteBase rawMem witness h)
    (QuotientReplacement.quotient_replacement rawMem witness h) e he Y heY
  exact closed_of_exact_singletons (quotientFiniteBase rawMem witness h).toBase Y hY

theorem quotient_inf_form (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    ∀ env, Sat (QuotientModel.quotientMember rawMem witness h) env Inf_form :=
  fun env => (bridge_Inf env).mpr (quotient_infinity rawMem witness h)

end SetTheory.BusyBeaver.ZFC.InductiveAttempts
