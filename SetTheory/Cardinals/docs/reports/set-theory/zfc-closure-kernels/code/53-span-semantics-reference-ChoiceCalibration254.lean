import BusyBeaver.ZFC.ConstructibleAbs
import BusyBeaver.ZFC.ConstructibleOrder
import BusyBeaver.ZFC.ZFCBoundPerm252

/-!
Standard-ZFC calibration of the actual
252-state blank machine. The constructible subtype supplies its own ZF bundle,
Power, Regularity and V=L. Choice is proved inside that subtype, not assumed
of the ambient model. Syntactic refutation transfer uses the existing external
first-order completeness theorem. No PA-internal representation is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.ChoiceCalibration254

open Constructible ConstructibleZF InternalOrd
open LeanProofs.BoundedZFCConsistency

universe u

section Models
variable {V : Type u} {mem : V → V → Prop}

/-- Choice in L follows from its own ZF, Power, Regularity and internal V=L. -/
theorem constructible_choice (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) :
    ChoiceSem (memL H hP) :=
  ConstructibleOrder.choice_of_VL (L_zfAxioms H hR hP)
    (L_regular H hR hP) (L_power H hR hP) (ConstructibleAbs.vEqL H hR hP)

/-- Every actual sealed ZFC axiom holds in the constructible subtype. -/
theorem constructible_models_ZFC (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (v : Nat → {x // InL H hP x}) :
    ∀ f, ZFCax_s f → Sat (memL H hP) v f := by
  intro f hf
  rcases hf with hf | rfl
  · exact L_models_ZF H hR hP v f hf
  · exact (bridge_Choice_sealed.mpr (constructible_choice H hR hP)) v

/-- An explicit constructible empty ordinal prevents an empty-domain shortcut. -/
theorem constructible_nonempty (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) :
    Nonempty {x // InL H hP x} :=
  ⟨⟨vempty H, inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))⟩⟩

/-- Any ordinary ZF model supplies a model witnessing Con(ZFC), externally. -/
theorem zfc_consistent_of_zf_model (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) :
    ¬ BProv ZFCax_s [] Form.fBot := by
  obtain ⟨x⟩ := constructible_nonempty H hR hP
  intro hf
  exact soundness_BProv hf (fun _ => x)
    (constructible_models_ZFC H hR hP (fun _ => x))
    (fun _ hNil => by cases hNil)
end Models

/-- Refutations transfer through model construction and external completeness.
This is only a refutation comparison, not same-domain model inclusion. -/
theorem zf_refutation_of_zfc (hf : BProv ZFCax_s [] Form.fBot) :
    BProv ZFax_s [] Form.fBot := by
  apply completeness_inf_context ZFax_s [] Form.fBot Sentences_ZF
  intro D mem v hmodel _
  obtain ⟨H, hP, hR⟩ := ZFNative.models_ZF mem v hmodel
  exact zfc_consistent_of_zf_model H hR hP hf

theorem zf_refutation_iff_zfc :
    BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨fun hf => BProv_theory_mono (fun _ h => Or.inl h) hf, zf_refutation_of_zfc⟩

theorem zf_consistency_iff_zfc :
    (¬ BProv ZFax_s [] Form.fBot) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr zf_refutation_iff_zfc

/-- The closed binary endpoint includes actual start0, whole boot and all sites. -/
theorem blank_halts_iff_zfc_refutation :
    BinaryPerm252.BlankHalts machinePerm252 ↔ BProv ZFCax_s [] Form.fBot :=
  BinaryPerm252.blank_halts_iff_zf_refutation.trans zf_refutation_iff_zfc

/-- External metatheorem for the literal 252-state blank machine. -/
theorem nonhalting_iff_zfc_consistency :
    (¬ BinaryPerm252.BlankHalts machinePerm252) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.ChoiceCalibration254

