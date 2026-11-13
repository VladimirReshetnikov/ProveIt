import BusyBeaver.ZFC.QuotientModel

/-! Actual formula-indexed Separation in the bisimulation quotient of CP/GIC (`KQ1Separation`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientSeparation

open Form ProfileCollection ProfileAxioms ProfileModel CompositionModel

universe u
variable {V : Type u}

abbrev separationRename := KQ1Separation.separationRename

theorem separation_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem
      (SeparationChoice mem a (fun z => QuotientModel.RelSat mem (scons z env) phi)) :=
  KQ1Separation.separation_instance mem h a phi env

/-- Only a sequence of representatives of an already supplied quotient environment. -/
noncomputable abbrev liftEnv (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (env : Nat → QuotientModel.Domain mem witness h) : Nat → V :=
  KQ1Separation.liftEnv mem witness (QuotientModel.ofCPGIC mem witness h) env

theorem mk_liftEnv (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (env : Nat → QuotientModel.Domain mem witness h) (i : Nat) :
    QuotientModel.mk mem witness h (liftEnv mem witness h env i) = env i :=
  KQ1Separation.mk_liftEnv mem witness (QuotientModel.ofCPGIC mem witness h) env i

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
