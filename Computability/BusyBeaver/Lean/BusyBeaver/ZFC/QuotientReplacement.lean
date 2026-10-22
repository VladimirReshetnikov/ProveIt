import BusyBeaver.ZFC.QuotientModel
import BusyBeaver.ZFC.KQ1Replacement

/-! Actual formula-indexed Replacement in the CP/GIC bisimulation quotient (`KQ1Replacement`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientReplacement

open ProfileModel

universe u
variable {V : Type u}

/-- The full quotient satisfies the actual semantic `ZFAxioms.repl` interface. -/
theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → QuotientModel.Domain mem witness h)
    (hFunctional : Functional (relOf (QuotientModel.quotientMember mem witness h) phi env))
    (a : QuotientModel.Domain mem witness h) :
    ∃ b, ∀ y, QuotientModel.quotientMember mem witness h y b ↔
      ∃ x, QuotientModel.quotientMember mem witness h x a ∧
        relOf (QuotientModel.quotientMember mem witness h) phi env y x :=
  KQ1Replacement.quotient_replacement mem witness (QuotientModel.ofCPGIC mem witness h)
    phi env hFunctional a

/-- Every repository Replacement formula holds under every quotient valuation. -/
theorem quotient_repl_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ phi env, SetTheory.Sat (QuotientModel.quotientMember mem witness h) env (Repl_form phi) :=
  KQ1Replacement.quotient_repl_form mem witness (QuotientModel.ofCPGIC mem witness h)

end SetTheory.BusyBeaver.ZFC.QuotientReplacement
