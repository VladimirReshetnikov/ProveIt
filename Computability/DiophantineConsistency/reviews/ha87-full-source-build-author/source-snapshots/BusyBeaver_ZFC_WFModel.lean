import BusyBeaver.ZFC.WFModelCore
import BusyBeaver.ZFC.WellFoundedPart
import BusyBeaver.ZFC.QuotientZF0
import BusyBeaver.ZFC.QuotientCPGIC

/-! Compatibility wrapper and CPGIC specialization; public names are preserved. -/

namespace SetTheory.BusyBeaver.ZFC.WFModel
open Form WellFoundedPart WFRelativization
universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The needed closure is supplied by the existing literal GIC witness case. -/
theorem quotient_models_ZF (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem)
    (env : Nat → Domain (QuotientModel.quotientMember rawMem witness h)) :
    ∀ phi, ZFax_s phi →
      Sat (domainMem (QuotientModel.quotientMember rawMem witness h)) env phi :=
  domain_models_ZF (QuotientZF0.quotient_zfAxioms rawMem witness h)
    (quotient_wf_closure rawMem witness h) (QuotientPower.quotient_power rawMem witness h) env

end SetTheory.BusyBeaver.ZFC.WFModel
