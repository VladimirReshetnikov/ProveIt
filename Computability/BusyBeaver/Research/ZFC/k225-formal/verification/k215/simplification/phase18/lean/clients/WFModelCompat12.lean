import BusyBeaver.ZFC.WFModel
import BusyBeaver.ZFC.WFTheory

namespace SetTheory.BusyBeaver.ZFC.WFModelCompat12
open Form WellFoundedPart WFRelativization WFModel
universe u
variable {V : Type u} {mem : V → V → Prop}

theorem domain_axioms (H : ZFAxioms mem) (hc : ClosedWF mem) :
    ZFAxioms (domainMem mem) := domain_zfAxioms H hc

theorem domain_models (H : ZFAxioms mem) (hc : ClosedWF mem)
    (hp : PSCCalibration.PowerSets mem) (env : Nat → Domain mem) :
    ∀ phi, ZFax_s phi → Sat (domainMem mem) env phi :=
  domain_models_ZF H hc hp env

theorem quotient_models (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem)
    (env : Nat → Domain (QuotientModel.quotientMember rawMem witness h)) :
    ∀ phi, ZFax_s phi →
      Sat (domainMem (QuotientModel.quotientMember rawMem witness h)) env phi :=
  quotient_models_ZF rawMem witness h env
end SetTheory.BusyBeaver.ZFC.WFModelCompat12

#print axioms SetTheory.BusyBeaver.ZFC.WFModelCompat12.domain_axioms
#print axioms SetTheory.BusyBeaver.ZFC.WFModelCompat12.domain_models
#print axioms SetTheory.BusyBeaver.ZFC.WFModelCompat12.quotient_models
