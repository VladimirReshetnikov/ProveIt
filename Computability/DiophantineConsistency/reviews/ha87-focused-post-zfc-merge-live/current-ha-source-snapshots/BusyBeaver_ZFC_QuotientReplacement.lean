import BusyBeaver.ZFC.QuotientSeparation
import BusyBeaver.ZFC.KQ1Replacement

/-! Actual formula-indexed Replacement in the CP/GIC bisimulation quotient (`KQ1Replacement`). -/

namespace SetTheory.BusyBeaver.ZFC.QuotientReplacement

open Form ProfileCollection ProfileComposition ProfileAxioms ProfileModel CompositionModel
open DeepPositiveClosure

universe u
variable {V : Type u}

abbrev replacementChoiceForm := KQ1Replacement.replacementChoiceForm

theorem equalityFree_replacementChoiceForm (phi : Form) :
    EqualityFree (replacementChoiceForm phi) :=
  KQ1Replacement.equalityFree_replacementChoiceForm phi

theorem sat_replacementChoiceForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (replacementChoiceForm phi) (scons a env) x y ↔
      ReplacementChoice mem a
        (fun u v => QuotientModel.RelSat mem (scons v (scons u env)) phi) x y :=
  KQ1Replacement.sat_replacementChoiceForm mem phi a env x y

theorem replacement_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem (ReplacementChoice mem a
      (fun x y => QuotientModel.RelSat mem (scons y (scons x env)) phi)) :=
  KQ1Replacement.replacement_instance mem h a phi env

/-- Partial functionality on the interpreted domain suffices for this image. -/
theorem interpreted_replacement (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (a : V) (phi : Form) (env : Nat → V)
    (hFunctional : ∀ x y z, Member mem x a →
      QuotientModel.RelSat mem (scons y (scons x env)) phi →
      QuotientModel.RelSat mem (scons z (scons x env)) phi → Eqv mem y z) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧
      QuotientModel.RelSat mem (scons z (scons x env)) phi :=
  KQ1Replacement.interpreted_replacement mem witness (QuotientModel.ofCPGIC mem witness h)
    a phi env hFunctional

/-- Formula relations under any quotient valuation agree with their lifted
interpretations; source slot0 is output and slot1 is input. -/
theorem quotient_relOf (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → QuotientModel.Domain mem witness h) (x y : V) :
    relOf (QuotientModel.quotientMember mem witness h) phi env
      (QuotientModel.mk mem witness h y) (QuotientModel.mk mem witness h x) ↔
    QuotientModel.RelSat mem
      (scons y (scons x (QuotientSeparation.liftEnv mem witness h env))) phi :=
  KQ1Replacement.quotient_relOf mem witness (QuotientModel.ofCPGIC mem witness h) phi env x y

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
