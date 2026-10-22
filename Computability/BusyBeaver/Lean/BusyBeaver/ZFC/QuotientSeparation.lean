import BusyBeaver.ZFC.QuotientModel

/-! Actual formula-indexed Separation in the bisimulation quotient of CP/GIC (`KQ1Separation`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientSeparation

open Form ProfileCollection ProfileAxioms ProfileModel CompositionModel

universe u
variable {V : Type u}

abbrev separationRename := KQ1Separation.separationRename

/-- The full quotient has Separation for every actual formula and parameter valuation.
This has exactly the semantic shape of the repository's ZFAxioms.sep field. -/
theorem quotient_separation (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → QuotientModel.Domain mem witness h)
    (a : QuotientModel.Domain mem witness h) :
    ∃ b, ∀ x, QuotientModel.quotientMember mem witness h x b ↔
      QuotientModel.quotientMember mem witness h x a ∧
        SetTheory.Sat (QuotientModel.quotientMember mem witness h) (scons x env) phi :=
  KQ1Separation.quotient_separation mem witness (QuotientModel.ofCPGIC mem witness h) phi env a

/-- Every repository Separation formula holds under every quotient valuation. -/
theorem quotient_sep_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ phi env, SetTheory.Sat (QuotientModel.quotientMember mem witness h) env (Sep_form phi) :=
  KQ1Separation.quotient_sep_form mem witness (QuotientModel.ofCPGIC mem witness h)

end SetTheory.BusyBeaver.ZFC.QuotientSeparation
