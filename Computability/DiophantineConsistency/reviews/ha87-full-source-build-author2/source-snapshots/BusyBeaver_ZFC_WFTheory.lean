import BusyBeaver.ZFC.WFModel
import BusyBeaver.ZFC.ZFNative

/-!
The native numerical calculus and ZF with Foundation are equiconsistent.

The reverse comparison builds the internally well-founded part of the
CP/GIC quotient. Its closure uses the actual global-image collection instance
already available there; no claim that arbitrary ZF0 models satisfy full
Collection is needed. Model soundness and the existing numerical completeness
adapter supply the finite-refutation consequences. Choice and the internal
arithmetic proof-code comparison remain separate.
-/

namespace SetTheory.BusyBeaver.ZFC.WFTheory
open WellFoundedPart
universe u
variable {V : Type u}

/-- The actual quotient WF model has an explicit inhabitant and valuation. -/
theorem zf_consistent_of_model (mem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC mem) : ¬ BProv ZFax_s [] Form.fBot := by
  obtain ⟨x⟩ := quotient_domain_nonempty mem witness h
  intro hf
  exact soundness_BProv hf (fun _ => x)
    (WFModel.quotient_models_ZF mem witness h (fun _ => x))
    (fun _ hNil => by cases hNil)

/-- A refutation of ordinary ZF forces numerical falsity. -/
theorem c254_of_zf_refutation (hf : BProv ZFax_s [] Form.fBot) :
    Code254.C254 Code254.F := by
  apply Code254.c254_complete
  intro D mem hirr hBundle valuation
  exact zf_consistent_of_model mem (valuation 0)
    (Code254GIC.modelsCPGIC_of_encBundle mem hirr valuation hBundle) hf

/-- This comparison includes Foundation and Power, with no Choice axiom. -/
theorem c254_refutation_iff_zf :
    Code254.C254 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨fun h => ZFNative.zf_refutation_of_native
      (NativeTheory254.c254_refutation_iff.mp h), c254_of_zf_refutation⟩

theorem native_refutation_iff_zf :
    BProv NativeTheory254.NativeAx [] Form.fBot ↔ BProv ZFax_s [] Form.fBot :=
  NativeTheory254.c254_refutation_iff.symm.trans c254_refutation_iff_zf

theorem native_consistency_iff_zf :
    (¬ BProv NativeTheory254.NativeAx [] Form.fBot) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr native_refutation_iff_zf

#print axioms zf_consistent_of_model
#print axioms c254_of_zf_refutation
#print axioms c254_refutation_iff_zf
#print axioms native_refutation_iff_zf
#print axioms native_consistency_iff_zf

end SetTheory.BusyBeaver.ZFC.WFTheory
