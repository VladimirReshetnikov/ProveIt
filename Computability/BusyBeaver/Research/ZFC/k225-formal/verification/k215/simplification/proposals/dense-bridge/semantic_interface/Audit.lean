import BusyBeaver.ZFC.WFModelCore
import BusyBeaver.ZFC.PSCCalibration

namespace PowerSetsExtractionAudit

open SetTheory SetTheory.BusyBeaver.ZFC

universe u

/-- The moved declaration has exactly the original definitional content. -/
theorem interface_eq {V : Type u} (mem : V → V → Prop) :
    PSCCalibration.PowerSets mem =
      (∀ a, ∃ p, ∀ y, mem y p ↔ SetTheory.Sub mem y a) := rfl

/-- The existing well-founded model theorem still consumes the same public type. -/
example {V : Type u} (mem : V → V → Prop)
    (H : ZFAxioms mem) (hc : WFModel.ClosedWF mem)
    (hp : PSCCalibration.PowerSets mem)
    (env : Nat → WellFoundedPart.Domain mem) :
    ∀ phi, ZFax_s phi → Sat (WellFoundedPart.domainMem mem) env phi :=
  WFModel.domain_models_ZF H hc hp env

#print axioms interface_eq
#print axioms WFModel.domain_models_ZF
#print axioms PSCCalibration.psc_iff_zfAxioms

end PowerSetsExtractionAudit
