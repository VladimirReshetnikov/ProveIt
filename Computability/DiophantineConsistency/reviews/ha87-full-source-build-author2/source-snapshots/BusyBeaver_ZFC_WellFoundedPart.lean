import BusyBeaver.ZFC.WellFoundedPartCore
import BusyBeaver.ZFC.FiniteSets
import BusyBeaver.ZFC.QuotientCPGIC

namespace SetTheory.BusyBeaver.ZFC.WellFoundedPart

open Form PositiveClosure DeepPositiveClosure ProfileCollection ProfileSyntax

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The actual quotient supplies the fixed native GIC instance and small base. -/
theorem quotient_wf_closure (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem)
    (a : QuotientModel.Domain rawMem witness h)
    (ha : ∀ x, QuotientModel.quotientMember rawMem witness h x a →
      WF (QuotientModel.quotientMember rawMem witness h) x) :
    WF (QuotientModel.quotientMember rawMem witness h) a :=
  wf_closure (FiniteSets.quotientBase rawMem witness h) a
    (QuotientCPGIC.quotient_fullGIC rawMem witness h witnessForm (fun _ => a)) ha

theorem quotient_domain_nonempty (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    Nonempty (Domain (QuotientModel.quotientMember rawMem witness h)) := by
  obtain ⟨e, he⟩ := QuotientBasic.quotient_empty rawMem witness h
  exact ⟨⟨e, wf_empty (FiniteSets.quotientBase rawMem witness h) e he⟩⟩

end SetTheory.BusyBeaver.ZFC.WellFoundedPart
